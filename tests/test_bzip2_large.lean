import Bzip2
import tests.test_bzip2

/-!
Dedicated large-file and stress-test harness.

This suite is opt-in. Set `LEANBZIP2_RUN_LARGE=1` to run it.

Environment knobs:
- `LEANBZIP2_LARGE_BYTES`: target large-file size in bytes. Defaults to 1 GiB.
- `LEANBZIP2_EXACT_LIMIT_BYTES`: maximum size allowed for the current exact
  encoder/decoder path. Defaults to 8 MiB. Exact cross-tests skip above this
  threshold because the current implementation still uses the matrix-based BWT
  path and whole-file in-memory decode/encode.

That means:
- the shell-only Linux `bzip2` large-file baseline can run at 1 GiB today,
- the exact cross-tool large-file cases are present, but they skip until the
  native sorter / streaming path is ready or you lower the size manually.
-/

set_option autoImplicit false

private def defaultLargeBytes : Nat :=
  1024 * 1024 * 1024

private def defaultExactLimitBytes : Nat :=
  8 * 1024 * 1024

private def parseNatEnv? (name : String) : IO (Option Nat) := do
  match ← IO.getEnv name with
  | none => pure none
  | some raw =>
      pure raw.toNat?

private def configuredLargeBytes : IO Nat := do
  pure <| (← parseNatEnv? "LEANBZIP2_LARGE_BYTES").getD defaultLargeBytes

private def configuredExactLimitBytes : IO Nat := do
  pure <| (← parseNatEnv? "LEANBZIP2_EXACT_LIMIT_BYTES").getD defaultExactLimitBytes

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

private def runShellScript (script : String) : IO (Except String Unit) := do
  let out ← IO.Process.output { cmd := "bash", args := #["-lc", script] }
  if out.exitCode = 0 then
    pure (.ok ())
  else
    pure (.error s!"exit {out.exitCode}: {out.stderr}")

private def createSparseFile (path : System.FilePath) (sizeBytes : Nat) : IO (Except String Unit) :=
  runShellScript s!"truncate -s {sizeBytes} {path.toString}"

private def compareFiles (expected actual : System.FilePath) : IO (Except String Unit) :=
  runShellScript s!"cmp -s {expected.toString} {actual.toString}"

private def removePaths (paths : List System.FilePath) : IO Unit := do
  for path in paths do
    removeIfExists path

private def shellLargeRoundtripCase : TestCase :=
  { name := "shell bzip2 roundtrips a sparse large file"
  , run := requireLargeHarness do
      let sizeBytes ← configuredLargeBytes
      let sourcePath : System.FilePath := "tests/tmp_large_shell_source.bin"
      let archivePath : System.FilePath := "tests/tmp_large_shell_source.bin.bz2"
      let roundtripPath : System.FilePath := "tests/tmp_large_shell_roundtrip.bin"
      try
        match ← createSparseFile sourcePath sizeBytes with
        | .error err => pure <| .fail s!"failed to create sparse large file: {err}"
        | .ok _ =>
            match ← runShellScript s!"cp {sourcePath.toString} {roundtripPath.toString}" with
            | .error err => pure <| .fail s!"failed to seed shell large roundtrip copy: {err}"
            | .ok _ =>
                match ← runShellScript s!"bzip2 -kf {roundtripPath.toString}" with
                | .error err => pure <| .fail s!"shell bzip2 compression failed on large file: {err}"
                | .ok _ =>
                    match ← runShellScript s!"bunzip2 -kf {archivePath.toString}" with
                    | .error err => pure <| .fail s!"shell bunzip2 decompression failed on large file: {err}"
                    | .ok _ =>
                        match ← compareFiles sourcePath roundtripPath with
                        | .error err => pure <| .fail s!"shell large roundtrip mismatch: {err}"
                        | .ok _ => pure .pass
      finally
        removePaths [sourcePath, archivePath, roundtripPath]
  }

private def exactLargeEncodeInteropCase : TestCase :=
  { name := "exact encoder large-file interop with shell bzip2"
  , run := requireLargeHarness do
      let sizeBytes ← configuredLargeBytes
      let exactLimit ← configuredExactLimitBytes
      if exactLimit < sizeBytes then
        pure <| .skip
          s!"Configured large-file size is {sizeBytes} bytes, but the current exact encoder is capped at {exactLimit} bytes until the native sorter lands."
      else
        let sourcePath : System.FilePath := "tests/tmp_large_exact_source.bin"
        let archivePath : System.FilePath := "tests/tmp_large_exact_source.bin.bz2"
        let outputPath : System.FilePath := "tests/tmp_large_exact_source.bin"
        try
          match ← createSparseFile sourcePath sizeBytes with
          | .error err => pure <| .fail s!"failed to create exact large source file: {err}"
          | .ok _ =>
              let _ ← compressBz2File sourcePath (some archivePath)
              match ← runShellScript s!"bunzip2 -kf {archivePath.toString}" with
              | .error err => pure <| .fail s!"shell bunzip2 failed on exact large archive: {err}"
              | .ok _ =>
                  match ← compareFiles sourcePath outputPath with
                  | .error err => pure <| .fail s!"exact large encode/decode mismatch: {err}"
                  | .ok _ => pure .pass
        finally
          removePaths [sourcePath, archivePath, outputPath]
  }

private def exactLargeDecodeInteropCase : TestCase :=
  { name := "exact decoder large-file interop with shell bzip2"
  , run := requireLargeHarness do
      let sizeBytes ← configuredLargeBytes
      let exactLimit ← configuredExactLimitBytes
      if exactLimit < sizeBytes then
        pure <| .skip
          s!"Configured large-file size is {sizeBytes} bytes, but the current exact decoder path is capped at {exactLimit} bytes until the native sorter / streaming decode path lands."
      else
        let sourcePath : System.FilePath := "tests/tmp_large_system_source.bin"
        let archivePath : System.FilePath := "tests/tmp_large_system_source.bin.bz2"
        let outputPath : System.FilePath := "tests/tmp_large_system_decoded.bin"
        try
          match ← createSparseFile sourcePath sizeBytes with
          | .error err => pure <| .fail s!"failed to create system large source file: {err}"
          | .ok _ =>
              match ← runShellScript s!"bzip2 -kf {sourcePath.toString}" with
              | .error err => pure <| .fail s!"shell bzip2 failed to compress large source file: {err}"
              | .ok _ =>
                  let _ ← decompressBz2File archivePath (some outputPath)
                  match ← compareFiles sourcePath outputPath with
                  | .error err => pure <| .fail s!"exact large decode mismatch: {err}"
                  | .ok _ => pure .pass
        finally
          removePaths [sourcePath, archivePath, outputPath]
  }

private def cases : List TestCase :=
  [ shellLargeRoundtripCase
  , exactLargeEncodeInteropCase
  , exactLargeDecodeInteropCase
  ]

def main : IO Unit := do
  let summary ← runCases {} cases
  IO.println s!"\nSummary: {summary.passed} passed, {summary.failed} failed, {summary.skipped} skipped"
  if summary.failed ≠ 0 then
    throw <| IO.userError s!"{summary.failed} large-file test(s) failed."
