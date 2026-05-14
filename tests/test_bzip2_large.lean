import Bzip2
import tests.test_bzip2

/-!
Dedicated large-file and stress-test harness.

This suite is opt-in. Set `LEANBZIP2_RUN_LARGE=1` to run it.

Environment knobs:
- `LEANBZIP2_LARGE_BYTES`: GB-scale target size in bytes. Defaults to 1 GiB.
- `LEANBZIP2_EXACT_LARGE_BYTES`: exact sparse interop target size in bytes.
  Defaults to 16 MiB.
- `LEANBZIP2_MULTIMEG_BYTES`: size for multi-megabyte text/binary cases.
  Defaults to 16 MiB.
- `LEANBZIP2_INCOMPRESSIBLE_BYTES`: size for the incompressible large-file case.
  Defaults to 64 MiB.
- `LEANBZIP2_MANY_BLOCKS_BYTES`: size for the many-blocks exact interop case.
  Defaults to 64 MiB.

The exact file helpers now process raw input block by block and decode blocks
directly to disk, so this harness exercises honest file-scale behavior rather
than only small in-memory archives.
-/

set_option autoImplicit false

private def defaultLargeBytes : Nat :=
  1024 * 1024 * 1024

private def defaultMultiMegBytes : Nat :=
  16 * 1024 * 1024

private def defaultExactLargeBytes : Nat :=
  16 * 1024 * 1024

private def defaultIncompressibleBytes : Nat :=
  64 * 1024 * 1024

private def defaultManyBlocksBytes : Nat :=
  64 * 1024 * 1024

private def parseNatEnv? (name : String) : IO (Option Nat) := do
  match ← IO.getEnv name with
  | none => pure none
  | some raw => pure raw.toNat?

private def configuredLargeBytes : IO Nat := do
  pure <| (← parseNatEnv? "LEANBZIP2_LARGE_BYTES").getD defaultLargeBytes

private def configuredMultiMegBytes : IO Nat := do
  pure <| (← parseNatEnv? "LEANBZIP2_MULTIMEG_BYTES").getD defaultMultiMegBytes

private def configuredExactLargeBytes : IO Nat := do
  pure <| (← parseNatEnv? "LEANBZIP2_EXACT_LARGE_BYTES").getD defaultExactLargeBytes

private def configuredIncompressibleBytes : IO Nat := do
  pure <| (← parseNatEnv? "LEANBZIP2_INCOMPRESSIBLE_BYTES").getD defaultIncompressibleBytes

private def configuredManyBlocksBytes : IO Nat := do
  pure <| (← parseNatEnv? "LEANBZIP2_MANY_BLOCKS_BYTES").getD defaultManyBlocksBytes

private def largeHarnessEnabled : IO Bool := do
  match ← IO.getEnv "LEANBZIP2_RUN_LARGE" with
  | some "1" => pure true
  | some "true" => pure true
  | some "TRUE" => pure true
  | _ => pure false

private def requireLargeHarness (action : IO TestOutcome) : IO TestOutcome := do
  if ← largeHarnessEnabled then
    requireShellBzip2 action
  else
    pure <| .skip
      "Set LEANBZIP2_RUN_LARGE=1 to enable the large-file harness."

private def runCommand (cmd : String) (args : Array String) : IO (Except String Unit) := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode = 0 then
    pure (.ok ())
  else
    pure (.error s!"exit {out.exitCode}: {out.stderr}")

private def createSparseFile (path : System.FilePath) (sizeBytes : Nat) : IO (Except String Unit) :=
  runCommand "truncate" #["-s", toString sizeBytes, path.toString]

private def compareFiles (expected actual : System.FilePath) : IO (Except String Unit) :=
  runCommand "cmp" #["-s", expected.toString, actual.toString]

private def copyFileWithSystemCp
    (sourcePath targetPath : System.FilePath) :
    IO (Except String Unit) :=
  runCommand "cp" #[sourcePath.toString, targetPath.toString]

private def removePaths (paths : List System.FilePath) : IO Unit := do
  for path in paths do
    removeIfExists path

private def appendRepeatedByte (out : ByteArray) (byte : UInt8) (count : Nat) : ByteArray :=
  Id.run do
    let mut out := out
    for _ in [0:count] do
      out := out.push byte
    pure out

private def repeatingTextChunk : ByteArray :=
  let line := "LeanBzip2 large text fixture line 0123456789 abcdefghijklmnopqrstuvwxyz.\n".toUTF8
  Id.run do
    let mut out := ByteArray.empty
    for _ in [0:1024] do
      out := out ++ line
    pure out

private def repeatingBinaryChunk : ByteArray :=
  Id.run do
    let mut out := ByteArray.empty
    for _ in [0:4096] do
      for n in [0:256] do
        out := out.push (UInt8.ofNat n)
    pure out

private def lcgStep (seed : UInt64) : UInt64 :=
  seed * 6364136223846793005 + 1442695040888963407

private def randomChunk (sizeBytes : Nat) (seed : UInt64) : ByteArray × UInt64 :=
  Id.run do
    let mut out := ByteArray.empty
    let mut seed := seed
    for _ in [0:sizeBytes] do
      seed := lcgStep seed
      out := out.push (UInt8.ofNat ((seed >>> 24).toNat))
    pure (out, seed)

private def writeRepeatedPatternFile
    (path : System.FilePath) (sizeBytes : Nat) (pattern : ByteArray) :
    IO (Except String Unit) := do
  if pattern.isEmpty then
    pure (.error "pattern generator returned an empty chunk")
  else
    try
      let handle ← IO.FS.Handle.mk path .write
      let mut remaining := sizeBytes
      while remaining > 0 do
        let chunk :=
          if pattern.size ≤ remaining then
            pattern
          else
            pattern.extract 0 remaining
        handle.write chunk
        remaining := remaining - chunk.size
      pure (.ok ())
    catch err =>
      pure (.error err.toString)

private def writePseudoRandomFile
    (path : System.FilePath) (sizeBytes : Nat) :
    IO (Except String Unit) := do
  try
    let handle ← IO.FS.Handle.mk path .write
    let chunkSize := 1024 * 1024
    let mut remaining := sizeBytes
    let mut seed : UInt64 := 0x123456789ABCDEF
    while remaining > 0 do
      let nextSize := min remaining chunkSize
      let (chunk, seed') := randomChunk nextSize seed
      handle.write chunk
      seed := seed'
      remaining := remaining - nextSize
    pure (.ok ())
  catch err =>
    pure (.error err.toString)

private def runExactInterop
    (sourcePath archivePath shellDecodedPath exactDecodedPath : System.FilePath)
    (blockSizeDigit : Nat) (shellCompressionArgs : Array String := #[]) :
    IO TestOutcome := do
  let shellArchivePath : System.FilePath := sourcePath.addExtension "bz2"
  try
    let _ ← compressBz2FileWithBlockSize blockSizeDigit sourcePath (some archivePath)
    match ← runSystemBzip2 #["-t", archivePath.toString] with
    | .error err => pure <| .fail s!"shell bzip2 -t rejected exact archive: {err}"
    | .ok _ =>
        match ← runSystemBzip2 #["-dkf", archivePath.toString] with
        | .error err => pure <| .fail s!"shell bzip2 failed to decode exact archive: {err}"
        | .ok _ =>
            match ← compareFiles sourcePath shellDecodedPath with
            | .error err => pure <| .fail s!"shell decode of our exact archive mismatched: {err}"
            | .ok _ =>
                match ← runSystemBzip2 (shellCompressionArgs ++ #["-kf", sourcePath.toString]) with
                | .error err => pure <| .fail s!"shell bzip2 failed to compress source file: {err}"
                | .ok _ =>
                    let _ ← decompressBz2File shellArchivePath (some exactDecodedPath)
                    match ← compareFiles sourcePath exactDecodedPath with
                    | .error err => pure <| .fail s!"our exact decoder mismatched shell-compressed output: {err}"
                    | .ok _ => pure .pass
  finally
    removePaths [archivePath, shellDecodedPath, shellArchivePath, exactDecodedPath]

private def runShellCompressedDecodeCheck
    (sourcePath exactDecodedPath : System.FilePath)
    (shellCompressionArgs : Array String := #[]) :
    IO TestOutcome := do
  let shellArchivePath : System.FilePath := sourcePath.addExtension "bz2"
  try
    match ← runSystemBzip2 (shellCompressionArgs ++ #["-kf", sourcePath.toString]) with
    | .error err => pure <| .fail s!"shell bzip2 failed to compress source file: {err}"
    | .ok _ =>
        let _ ← decompressBz2File shellArchivePath (some exactDecodedPath)
        match ← compareFiles sourcePath exactDecodedPath with
        | .error err => pure <| .fail s!"our exact decoder mismatched shell-compressed output: {err}"
        | .ok _ => pure .pass
  finally
    removePaths [shellArchivePath, exactDecodedPath]

private def runShellRoundtripCheck
    (sourcePath roundtripPath : System.FilePath)
    (shellCompressionArgs : Array String := #[]) :
    IO TestOutcome := do
  let archivePath : System.FilePath := roundtripPath.addExtension "bz2"
  try
    match ← copyFileWithSystemCp sourcePath roundtripPath with
    | .error err => pure <| .fail s!"failed to seed shell roundtrip copy: {err}"
    | .ok _ =>
        match ← runSystemBzip2 (shellCompressionArgs ++ #["-kf", roundtripPath.toString]) with
        | .error err => pure <| .fail s!"shell bzip2 compression failed: {err}"
        | .ok _ =>
            match ← runSystemBzip2 #["-dkf", archivePath.toString] with
            | .error err => pure <| .fail s!"shell bzip2 decompression failed: {err}"
            | .ok _ =>
                match ← compareFiles sourcePath roundtripPath with
                | .error err => pure <| .fail s!"shell roundtrip mismatch: {err}"
                | .ok _ => pure .pass
  finally
    removePaths [archivePath, roundtripPath]

private def shellLargeRoundtripCase : TestCase :=
  { name := "shell bzip2 roundtrips a sparse GB-scale file"
  , run := requireLargeHarness do
      let sizeBytes ← configuredLargeBytes
      let sourcePath : System.FilePath := "tests/tmp_large_shell_source.bin"
      let archivePath : System.FilePath := "tests/tmp_large_shell_roundtrip.bin.bz2"
      let roundtripPath : System.FilePath := "tests/tmp_large_shell_roundtrip.bin"
      try
        match ← createSparseFile sourcePath sizeBytes with
        | .error err => pure <| .fail s!"failed to create sparse large file: {err}"
        | .ok _ =>
            match ← copyFileWithSystemCp sourcePath roundtripPath with
            | .error err => pure <| .fail s!"failed to seed shell large roundtrip copy: {err}"
            | .ok _ =>
                match ← runSystemBzip2 #["-kf", roundtripPath.toString] with
                | .error err => pure <| .fail s!"shell bzip2 compression failed on large file: {err}"
                | .ok _ =>
                    match ← runSystemBzip2 #["-dkf", archivePath.toString] with
                    | .error err => pure <| .fail s!"shell bzip2 decompression failed on large file: {err}"
                    | .ok _ =>
                        match ← compareFiles sourcePath roundtripPath with
                        | .error err => pure <| .fail s!"shell large roundtrip mismatch: {err}"
                        | .ok _ => pure .pass
      finally
        removePaths [sourcePath, archivePath, roundtripPath]
  }

private def exactLargeSparseInteropCase : TestCase :=
  { name := "exact interop handles a sparse large file"
  , run := requireLargeHarness do
      let sizeBytes ← configuredExactLargeBytes
      let sourcePath : System.FilePath := "tests/tmp_large_sparse_source.bin"
      let archivePath : System.FilePath := "tests/tmp_large_sparse_exact.bz2"
      let shellDecodedPath : System.FilePath := "tests/tmp_large_sparse_exact"
      let exactDecodedPath : System.FilePath := "tests/tmp_large_sparse_decoded.bin"
      try
        match ← createSparseFile sourcePath sizeBytes with
        | .error err => pure <| .fail s!"failed to create sparse exact source file: {err}"
        | .ok _ =>
            runExactInterop sourcePath archivePath shellDecodedPath exactDecodedPath 9 #["-9"]
      finally
        removePaths [sourcePath]
  }

private def largeTextInteropCase : TestCase :=
  { name := "shell bzip2 handles a multi-megabyte text file"
  , run := requireLargeHarness do
      let sizeBytes ← configuredMultiMegBytes
      let sourcePath : System.FilePath := "tests/tmp_large_text_source.txt"
      let roundtripPath : System.FilePath := "tests/tmp_large_text_roundtrip.txt"
      try
        match ← writeRepeatedPatternFile sourcePath sizeBytes repeatingTextChunk with
        | .error err => pure <| .fail s!"failed to create large text file: {err}"
        | .ok _ =>
            runShellRoundtripCheck sourcePath roundtripPath #["-9"]
      finally
        removePaths [sourcePath]
  }

private def largeBinaryInteropCase : TestCase :=
  { name := "shell bzip2 handles a multi-megabyte binary file"
  , run := requireLargeHarness do
      let sizeBytes ← configuredMultiMegBytes
      let sourcePath : System.FilePath := "tests/tmp_large_binary_source.bin"
      let roundtripPath : System.FilePath := "tests/tmp_large_binary_roundtrip.bin"
      try
        match ← writeRepeatedPatternFile sourcePath sizeBytes repeatingBinaryChunk with
        | .error err => pure <| .fail s!"failed to create large binary file: {err}"
        | .ok _ =>
            runShellRoundtripCheck sourcePath roundtripPath #["-9"]
      finally
        removePaths [sourcePath]
  }

private def incompressibleLargeInteropCase : TestCase :=
  { name := "shell bzip2 handles a large incompressible-style file"
  , run := requireLargeHarness do
      let sizeBytes ← configuredIncompressibleBytes
      let sourcePath : System.FilePath := "tests/tmp_large_random_source.bin"
      let roundtripPath : System.FilePath := "tests/tmp_large_random_roundtrip.bin"
      try
        match ← writePseudoRandomFile sourcePath sizeBytes with
        | .error err => pure <| .fail s!"failed to create large pseudo-random file: {err}"
        | .ok _ =>
            runShellRoundtripCheck sourcePath roundtripPath #["-9"]
      finally
        removePaths [sourcePath]
  }

private def manyBlocksInteropCase : TestCase :=
  { name := "shell bzip2 handles files spanning many exact blocks"
  , run := requireLargeHarness do
      let sizeBytes ← configuredManyBlocksBytes
      let sourcePath : System.FilePath := "tests/tmp_many_blocks_source.txt"
      let roundtripPath : System.FilePath := "tests/tmp_many_blocks_roundtrip.txt"
      try
        match ← writeRepeatedPatternFile sourcePath sizeBytes repeatingTextChunk with
        | .error err => pure <| .fail s!"failed to create many-blocks source file: {err}"
        | .ok _ =>
            runShellRoundtripCheck sourcePath roundtripPath #["-1"]
      finally
        removePaths [sourcePath]
  }

private def cases : List TestCase :=
  [ shellLargeRoundtripCase
  , exactLargeSparseInteropCase
  , largeTextInteropCase
  , largeBinaryInteropCase
  , incompressibleLargeInteropCase
  , manyBlocksInteropCase
  ]

def main : IO Unit := do
  let summary ← runCases {} cases
  IO.println s!"\nSummary: {summary.passed} passed, {summary.failed} failed, {summary.skipped} skipped"
  if summary.failed ≠ 0 then
    throw <| IO.userError s!"{summary.failed} large-file test(s) failed."
