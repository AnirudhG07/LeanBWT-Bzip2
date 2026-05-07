import Bzip2
import tests.test_bzip2

/-!
Shell-level interoperability tests for the exact `.bz2` path.

This harness first checks whether `bzip2` is available from the shell. When it
is present, the tests run real file-based compression/decompression commands and
compare the resulting bytes with the expected payloads. If `bzip2` is missing,
the cases are skipped rather than reported as failures.
-/

set_option autoImplicit false

private def exactShellRoundtripCase : TestCase :=
  { name := "shell bzip2 decompresses our exact bz2 file"
  , run := requireShellBzip2 do
      let input := byteArrayOfList <|
        [0, 0, 255, 254, 1, 2, 3, 65, 66, 67, 10, 200, 201, 202].map UInt8.ofNat
      let sourcePath : System.FilePath := "tests/tmp_shell_expected.bin"
      let archivePath : System.FilePath := "tests/tmp_shell_exact_roundtrip.bin.bz2"
      let outputPath : System.FilePath := "tests/tmp_shell_exact_roundtrip.bin"
      try
        IO.FS.writeBinFile sourcePath input
        let _ ← compressBz2File sourcePath (some archivePath)
        match ← runSystemBzip2 #["-t", archivePath.toString] with
        | .error err => pure <| .fail s!"shell bzip2 -t failed: {err}"
        | .ok _ =>
            match ← runSystemBzip2 #["-dkf", archivePath.toString] with
            | .error err => pure <| .fail s!"shell bzip2 decompression failed: {err}"
            | .ok _ =>
                let decoded ← IO.FS.readBinFile outputPath
                if decoded = input then
                  pure .pass
                else
                  pure <| .fail "shell bzip2 did not reproduce our exact encoded payload"
      finally
        removeIfExists sourcePath
        removeIfExists archivePath
        removeIfExists outputPath
  }

private def shellProducesArchiveOurDecoderReadsCase : TestCase :=
  { name := "our exact decoder reads shell bzip2 output"
  , run := requireShellBzip2 do
      let input := byteArrayOfList <|
        [42, 42, 42, 42, 1, 2, 3, 4, 255, 0, 13, 10, 90, 91, 92].map UInt8.ofNat
      let inputPath : System.FilePath := "tests/tmp_shell_source.bin"
      let archivePath : System.FilePath := "tests/tmp_shell_source.bin.bz2"
      let outputPath : System.FilePath := "tests/tmp_shell_decoded.bin"
      try
        IO.FS.writeBinFile inputPath input
        match ← runSystemBzip2 #["-9", "-kf", inputPath.toString] with
        | .error err => pure <| .fail s!"shell bzip2 compression failed: {err}"
        | .ok _ =>
            let _ ← decompressBz2File archivePath (some outputPath)
            let decoded ← IO.FS.readBinFile outputPath
            if decoded = input then
              pure .pass
            else
              pure <| .fail "our exact decoder did not match shell-compressed output"
      finally
        removeIfExists inputPath
        removeIfExists archivePath
        removeIfExists outputPath
  }

private def shellConcatenatedInteropCase : TestCase :=
  { name := "shell bzip2 handles concatenated exact bz2 streams"
  , run := requireShellBzip2 do
      let left := "left shell stream\nAAAAABBBBB\n".toUTF8
      let right := byteArrayOfList <| [0, 255, 0, 255, 7, 8, 9, 10, 11].map UInt8.ofNat
      let expected := appendByteArray left right
      let leftPath : System.FilePath := "tests/tmp_shell_concat_left.bin"
      let rightPath : System.FilePath := "tests/tmp_shell_concat_right.bin"
      let leftArchivePath : System.FilePath := "tests/tmp_shell_concat_left.bz2"
      let rightArchivePath : System.FilePath := "tests/tmp_shell_concat_right.bz2"
      let concatArchivePath : System.FilePath := "tests/tmp_shell_concat.bz2"
      let concatOutputPath : System.FilePath := "tests/tmp_shell_concat"
      try
        IO.FS.writeBinFile leftPath left
        IO.FS.writeBinFile rightPath right
        let _ ← compressBz2FileWithBlockSize 1 leftPath (some leftArchivePath)
        let _ ← compressBz2FileWithBlockSize 9 rightPath (some rightArchivePath)
        let leftArchive ← IO.FS.readBinFile leftArchivePath
        let rightArchive ← IO.FS.readBinFile rightArchivePath
        IO.FS.writeBinFile concatArchivePath (appendByteArray leftArchive rightArchive)
        match ← runSystemBzip2 #["-dkf", concatArchivePath.toString] with
        | .error err => pure <| .fail s!"shell bzip2 failed on concatenated exact streams: {err}"
        | .ok _ =>
            let decoded ← IO.FS.readBinFile concatOutputPath
            if decoded = expected then
              pure .pass
            else
              pure <| .fail "shell bzip2 did not decode concatenated exact streams correctly"
      finally
        removeIfExists leftPath
        removeIfExists rightPath
        removeIfExists leftArchivePath
        removeIfExists rightArchivePath
        removeIfExists concatArchivePath
        removeIfExists concatOutputPath
  }

private def cases : List TestCase :=
  [ exactShellRoundtripCase
  , shellProducesArchiveOurDecoderReadsCase
  , shellConcatenatedInteropCase
  ]


def main : IO Unit := do
  let summary ← runCases {} cases
  IO.println s!"\nSummary: {summary.passed} passed, {summary.failed} failed, {summary.skipped} skipped"
  if summary.failed ≠ 0 then
    throw <| IO.userError s!"{summary.failed} shell integration test(s) failed."
