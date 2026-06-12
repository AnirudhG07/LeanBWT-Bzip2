import Bzip2.Library

/-!
bzip2-compatible command-line interface.

Implements the core flag set and semantics of the reference `bzip2` tool:
in-place compression and decompression, `-t` integrity testing, stdin/stdout
filtering, clustered short flags (`-dkf9`), and bzip2-style exit codes
(`0` = ok, `1` = environmental problem or usage error, `2` = corrupt input,
`3` = internal error).

Known divergences from the reference tool, by design:
- file timestamps and ownership are not copied to outputs (no portable API),
- deprecated randomised blocks are rejected on decompression,
- the `BZIP2`/`BZIP` environment variables are not consulted.
-/

namespace BZip2.CLI

set_option autoImplicit false

/-- What the invocation should do with each input. -/
inductive OpMode
  | compress
  | decompress
  | test
deriving DecidableEq, Inhabited

/-- Parsed command-line configuration. -/
structure Options where
  mode : OpMode := .compress
  keep : Bool := false
  force : Bool := false
  toStdout : Bool := false
  quiet : Bool := false
  verbosity : Nat := 0
  blockSize : Nat := 9
  files : Array String := #[]
  showHelp : Bool := false
  showVersion : Bool := false
  showLicense : Bool := false
deriving Inhabited

def programName : String := "leanbzip2"

def versionLine : String :=
  s!"{programName} 0.1.0: exact-format bzip2 compressor/decompressor written in Lean 4"

def licenseText : String :=
  versionLine ++ "\n" ++
  "Distributed under the MIT license; see the LICENSE file in the source tree.\n" ++
  "The .bz2 format is due to Julian Seward's bzip2."

def usageText : String :=
  s!"usage: {programName} [flags and input files in any order]

   -h --help           print this message
   -d --decompress     force decompression
   -z --compress       force compression
   -k --keep           keep (don't delete) input files
   -f --force          overwrite existing output files
   -t --test           test compressed file integrity
   -c --stdout         output to standard out
   -q --quiet          suppress noncritical error messages
   -v --verbose        be verbose (a 2nd -v gives more)
   -L --license        display software license
   -V --version        display software version
   -s --small          accepted for compatibility (no effect)
   -1 .. -9            set block size to 100k .. 900k
      --fast           alias for -1
      --best           alias for -9

   If invoked as `bunzip2', default action is to decompress.
              as `bzcat', default action is to decompress to stdout.

   If no file names are given, {programName} compresses or decompresses
   from standard input to standard output."

private def applyShortFlag (opts : Options) (c : Char) : Except String Options :=
  match c with
  | 'd' => .ok { opts with mode := .decompress }
  | 'z' => .ok { opts with mode := .compress }
  | 't' => .ok { opts with mode := .test }
  | 'k' => .ok { opts with keep := true }
  | 'c' => .ok { opts with toStdout := true }
  | 'f' => .ok { opts with force := true }
  | 'q' => .ok { opts with quiet := true }
  | 'v' => .ok { opts with verbosity := opts.verbosity + 1 }
  | 's' => .ok opts
  | 'L' => .ok { opts with showLicense := true }
  | 'V' => .ok { opts with showVersion := true }
  | 'h' => .ok { opts with showHelp := true }
  | _ =>
    if '1' ≤ c ∧ c ≤ '9' then
      .ok { opts with blockSize := c.toNat - '0'.toNat }
    else
      .error s!"{programName}: Bad flag `-{c}'"

private def applyLongFlag (opts : Options) (flag : String) : Except String Options :=
  match flag with
  | "--decompress" => .ok { opts with mode := .decompress }
  | "--compress" => .ok { opts with mode := .compress }
  | "--test" => .ok { opts with mode := .test }
  | "--keep" => .ok { opts with keep := true }
  | "--stdout" => .ok { opts with toStdout := true }
  | "--force" => .ok { opts with force := true }
  | "--quiet" => .ok { opts with quiet := true }
  | "--verbose" => .ok { opts with verbosity := opts.verbosity + 1 }
  | "--small" => .ok opts
  | "--fast" => .ok { opts with blockSize := 1 }
  | "--best" => .ok { opts with blockSize := 9 }
  | "--license" => .ok { opts with showLicense := true }
  | "--version" => .ok { opts with showVersion := true }
  | "--help" => .ok { opts with showHelp := true }
  | "--repetitive-fast" => .ok opts
  | "--repetitive-best" => .ok opts
  | _ => .error s!"{programName}: Bad flag `{flag}'"

private def parseArgsAux : List String → Bool → Options → Except String Options
  | [], _, opts => .ok opts
  | arg :: rest, flagsDone, opts => do
      if flagsDone ∨ arg = "-" ∨ ¬ arg.startsWith "-" then
        parseArgsAux rest flagsDone { opts with files := opts.files.push arg }
      else if arg = "--" then
        parseArgsAux rest true opts
      else if arg.startsWith "--" then
        parseArgsAux rest flagsDone (← applyLongFlag opts arg)
      else
        let opts ← arg.toList.drop 1 |>.foldlM applyShortFlag opts
        parseArgsAux rest flagsDone opts

/-- Parse a bzip2-style argument list on top of argv0-derived defaults. -/
def parseArgs (args : List String) (base : Options := {}) : Except String Options :=
  parseArgsAux args false base

/-- Apply `bunzip2` / `bzcat` invocation-name defaults, like the reference tool. -/
def argv0Defaults (exeName : String) (opts : Options) : Options :=
  if exeName = "bunzip2" ∨ exeName.endsWith "bunzip2" then
    { opts with mode := .decompress }
  else if exeName = "bzcat" ∨ exeName.endsWith "bzcat" then
    { opts with mode := .decompress, toStdout := true }
  else
    opts

private def eprintln (msg : String) : IO Unit := do
  (← IO.getStderr).putStrLn msg

private def warn (opts : Options) (msg : String) : IO Unit := do
  if !opts.quiet then
    eprintln s!"{programName}: {msg}"

private def report (opts : Options) (msg : String) : IO Unit := do
  if opts.verbosity > 0 then
    eprintln msg

/-- Exit codes following the bzip2 convention. -/
def exitOk : UInt32 := 0
def exitEnv : UInt32 := 1
def exitCorrupt : UInt32 := 2
def exitInternal : UInt32 := 3

private def readChunkSize : USize := 65536

/--
Compress from a pull-based byte source to a sink, slicing the input into
exact block-size chunks so short reads (pipes, terminals) never produce
undersized blocks. Returns `(bytesIn, bytesOut)`.
-/
def compressStream (blockSizeDigit : Nat)
    (read : USize → IO ByteArray) (write : ByteArray → IO Unit) :
    IO (Except String (Nat × Nat)) := do
  let config ←
    match Bzip2.Format.BZ2.streamConfig? blockSizeDigit with
    | .ok config => pure config
    | .error err => return .error err
  let blockBytes := config.blockSizeBytes
  let mut state := Bzip2.Format.BZ2.StreamEncoderState.init config
  let mut buffer := ByteArray.empty
  let mut bytesIn := 0
  let mut done := false
  while !done do
    let chunk ← read readChunkSize
    if chunk.isEmpty then
      done := true
    else
      bytesIn := bytesIn + chunk.size
      buffer := buffer ++ chunk
      while blockBytes ≤ buffer.size do
        match Bzip2.Format.BZ2.StreamEncoderState.pushRawBlock? state
            (buffer.extract 0 blockBytes) with
        | .ok state' => state := state'
        | .error err => return .error err
        buffer := buffer.extract blockBytes buffer.size
  if !buffer.isEmpty then
    match Bzip2.Format.BZ2.StreamEncoderState.pushRawBlock? state buffer with
    | .ok state' => state := state'
    | .error err => return .error err
  let archive := Bzip2.Format.BZ2.StreamEncoderState.finish state
  write archive
  pure (.ok (bytesIn, archive.size))

/--
Decompress a fully-read archive to a sink. Returns the decoded byte count.
-/
def decompressStream (archive : ByteArray) (write : ByteArray → IO Unit) :
    IO (Except String Nat) := do
  let counter ← IO.mkRef 0
  let countedWrite (chunk : ByteArray) : IO Unit := do
    counter.modify (· + chunk.size)
    write chunk
  match ← Bzip2.Format.BZ2.decompressToSink? archive countedWrite with
  | .ok _ => pure (.ok (← counter.get))
  | .error err => pure (.error err)

private def readAll (read : USize → IO ByteArray) : IO ByteArray := do
  let mut out := ByteArray.empty
  let mut done := false
  while !done do
    let chunk ← read readChunkSize
    if chunk.isEmpty then
      done := true
    else
      out := out ++ chunk
  pure out

private def formatRatio (bytesIn bytesOut : Nat) : String :=
  let scaled := if bytesOut = 0 then 0 else bytesIn * 1000 / bytesOut
  s!"{scaled / 1000}.{(scaled % 1000 + 1000).toDigits 10 |>.drop 1 |> String.ofList}:1"

private def reportCompress (opts : Options) (name : String) (bytesIn bytesOut : Nat) : IO Unit :=
  report opts
    s!"  {name}: {formatRatio bytesIn bytesOut}, {bytesIn} in, {bytesOut} out."

/-- Output path for compression: `file` → `file.bz2`. -/
def compressedName (input : String) : String := input ++ ".bz2"

/--
Output path for decompression, following the reference tool's suffix rules.
Returns the output name and whether the suffix was recognized.
-/
def decompressedName (input : String) : String × Bool :=
  if input.endsWith ".bz2" then ((input.dropEnd 4).toString, true)
  else if input.endsWith ".bz" then ((input.dropEnd 3).toString, true)
  else if input.endsWith ".tbz2" then ((input.dropEnd 5).toString ++ ".tar", true)
  else if input.endsWith ".tbz" then ((input.dropEnd 4).toString ++ ".tar", true)
  else (input ++ ".out", false)

private def removeIfExists (path : String) : IO Unit := do
  if ← System.FilePath.pathExists path then
    IO.FS.removeFile path

private def finishOutput (opts : Options) (inputPath : String) : IO Unit := do
  if !opts.keep && !opts.toStdout && opts.mode ≠ .test then
    IO.FS.removeFile inputPath

private def checkOverwrite (opts : Options) (outPath : String) : IO Bool := do
  if (← System.FilePath.pathExists outPath) && !opts.force then
    warn opts s!"Output file {outPath} already exists."
    pure false
  else
    pure true

private def compressOneFile (opts : Options) (path : String) : IO UInt32 := do
  if !opts.toStdout && (path.endsWith ".bz2" || path.endsWith ".bz") then
    warn opts s!"Input file {path} already has .bz2 suffix."
    return exitEnv
  let input ← IO.FS.Handle.mk path .read
  if opts.toStdout then
    let stdout ← IO.getStdout
    match ← compressStream opts.blockSize input.read stdout.write with
    | .ok (bytesIn, bytesOut) =>
        stdout.flush
        reportCompress opts path bytesIn bytesOut
        pure exitOk
    | .error err =>
        warn opts err
        pure exitInternal
  else
    let outPath := compressedName path
    if !(← checkOverwrite opts outPath) then
      return exitEnv
    let output ← IO.FS.Handle.mk outPath .write
    match ← compressStream opts.blockSize input.read output.write with
    | .ok (bytesIn, bytesOut) =>
        reportCompress opts path bytesIn bytesOut
        finishOutput opts path
        pure exitOk
    | .error err =>
        warn opts err
        removeIfExists outPath
        pure exitInternal

private def decompressOneFile (opts : Options) (path : String) : IO UInt32 := do
  let archive ← IO.FS.readBinFile path
  if opts.toStdout then
    let stdout ← IO.getStdout
    match ← decompressStream archive stdout.write with
    | .ok _ =>
        stdout.flush
        report opts s!"  {path}: done"
        pure exitOk
    | .error err =>
        warn opts s!"{path}: {err}"
        pure exitCorrupt
  else
    let (outPath, guessed) := decompressedName path
    if !guessed then
      warn opts s!"Can't guess original name for {path} -- using {outPath}"
    if !(← checkOverwrite opts outPath) then
      return exitEnv
    let output ← IO.FS.Handle.mk outPath .write
    match ← decompressStream archive output.write with
    | .ok _ =>
        report opts s!"  {path}: done"
        finishOutput opts path
        pure exitOk
    | .error err =>
        warn opts s!"{path}: {err}"
        removeIfExists outPath
        pure exitCorrupt

private def testOneFile (opts : Options) (path : String) : IO UInt32 := do
  let archive ← IO.FS.readBinFile path
  match ← decompressStream archive (fun _ => pure ()) with
  | .ok _ =>
      report opts s!"  {path}: ok"
      pure exitOk
  | .error err =>
      warn opts s!"{path}: {err}"
      pure exitCorrupt

/-- Process stdin → stdout in the selected mode. -/
def runStdinStdout (opts : Options) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  match opts.mode with
  | .compress =>
      if (← stdout.isTty) && !opts.force then
        warn opts
          "I won't write compressed data to a terminal. Use -f to force, or pipe the output."
        return exitEnv
      match ← compressStream opts.blockSize stdin.read stdout.write with
      | .ok (bytesIn, bytesOut) =>
          stdout.flush
          reportCompress opts "(stdin)" bytesIn bytesOut
          pure exitOk
      | .error err =>
          warn opts err
          pure exitInternal
  | .decompress =>
      if (← stdin.isTty) && !opts.force then
        warn opts
          "I won't read compressed data from a terminal. Use -f to force, or pipe the input."
        return exitEnv
      let archive ← readAll stdin.read
      match ← decompressStream archive stdout.write with
      | .ok _ =>
          stdout.flush
          pure exitOk
      | .error err =>
          warn opts s!"(stdin): {err}"
          pure exitCorrupt
  | .test =>
      let archive ← readAll stdin.read
      match ← decompressStream archive (fun _ => pure ()) with
      | .ok _ =>
          report opts "  (stdin): ok"
          pure exitOk
      | .error err =>
          warn opts s!"(stdin): {err}"
          pure exitCorrupt

/-- Process one named input (or `-` for stdin), trapping IO errors as exit code 1. -/
def processOne (opts : Options) (path : String) : IO UInt32 := do
  try
    if path = "-" then
      runStdinStdout opts
    else if !(← System.FilePath.pathExists path) then
      warn opts s!"Can't open input file {path}: No such file or directory."
      pure exitEnv
    else if ← System.FilePath.isDir path then
      warn opts s!"Input file {path} is a directory."
      pure exitEnv
    else
      match opts.mode with
      | .compress => compressOneFile opts path
      | .decompress => decompressOneFile opts path
      | .test => testOneFile opts path
  catch e =>
    warn opts s!"{path}: {e}"
    pure exitEnv

/--
Best-effort invoked-as name. Lean's `main` does not receive `argv[0]` and
`IO.appPath` resolves symlinks, so on Linux read `/proc/self/cmdline`
(argv strings separated by NUL bytes) to honor `bunzip2`/`bzcat` symlinks.
-/
private def invokedName : IO String := do
  try
    let cmdline ← IO.FS.readBinFile "/proc/self/cmdline"
    let argv0Bytes := cmdline.toList.takeWhile (· ≠ 0)
    let argv0 := String.fromUTF8? (ByteArray.mk argv0Bytes.toArray) |>.getD ""
    if argv0.isEmpty then
      throw <| IO.userError "empty argv0"
    pure ((System.FilePath.mk argv0).fileName.getD argv0)
  catch _ =>
    try
      pure ((← IO.appPath).fileName.getD "")
    catch _ =>
      pure ""

/-- Main CLI driver. -/
def run (args : List String) : IO UInt32 := do
  let exeName ← invokedName
  let base := argv0Defaults exeName {}
  match parseArgs args base with
  | .error msg =>
      eprintln msg
      eprintln s!"{programName}: Try `{programName} --help' for more information."
      pure exitEnv
  | .ok opts =>
      if opts.showHelp then
        IO.println usageText
        pure exitOk
      else if opts.showVersion then
        IO.println versionLine
        pure exitOk
      else if opts.showLicense then
        IO.println licenseText
        pure exitOk
      else
        let files := if opts.files.isEmpty then #["-"] else opts.files
        let mut worst := exitOk
        for file in files do
          let code ← processOne opts file
          worst := max worst code
        pure worst

end BZip2.CLI
