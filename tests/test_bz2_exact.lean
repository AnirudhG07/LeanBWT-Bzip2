import Bzip2
import tests.test_bzip2

set_option autoImplicit false

open Bzip2.Format.BZ2

private def exactHeaderCase : TestCase :=
  { name := "exact empty-stream header and eos"
  , run := do
      match ← loadFixture "empty_level1.bz2.hex" with
      | .error err => pure <| .fail s!"fixture error: {err}"
      | .ok bytes =>
          match parseStreamHeader (BitReader.ofByteArray bytes) with
          | .error err => pure <| .fail s!"header parse error: {err}"
          | .ok (header, reader) =>
              if header.blockSizeDigit ≠ 1 ∨ header.blockSizeBytes ≠ 100000 then
                pure <| .fail "unexpected stream header contents"
              else
                match parseSection reader with
                | .error err => pure <| .fail s!"section parse error: {err}"
                | .ok (.eos trailer, _) =>
                    if trailer.streamCRC = 0 then
                      pure .pass
                    else
                      pure <| .fail "unexpected empty-stream CRC"
                | .ok (.block _, _) =>
                    pure <| .fail "expected end-of-stream marker, got block marker"
  }

private def exactBlockMetadataCase : TestCase :=
  { name := "exact block metadata and huffman metadata"
  , run := do
      match ← loadFixture "banana_level1.bz2.hex" with
      | .error err => pure <| .fail s!"fixture error: {err}"
      | .ok bytes =>
          match parseStreamHeader (BitReader.ofByteArray bytes) with
          | .error err => pure <| .fail s!"header parse error: {err}"
          | .ok (header, reader) =>
              if header.blockSizeDigit ≠ 1 then
                pure <| .fail "unexpected block-size digit"
              else
                match parseSection reader with
                | .error err => pure <| .fail s!"section parse error: {err}"
                | .ok (.eos _, _) =>
                    pure <| .fail "expected block marker, got end-of-stream marker"
                | .ok (.block metadata, _) =>
                    let expectedUsed : List UInt8 := [10, 97, 98, 110].map UInt8.ofNat
                    let alphaSize := metadata.header.alphaSize
                    if metadata.header.randomised then
                      pure <| .fail "fixture unexpectedly uses randomised blocks"
                    else if metadata.header.usedBytes ≠ expectedUsed then
                      pure <| .fail "unexpected used-byte map"
                    else if metadata.header.origPtr ≥ 7 then
                      pure <| .fail "origPtr is outside the expected block range"
                    else if ¬ (2 ≤ metadata.huffman.groupCount ∧ metadata.huffman.groupCount ≤ 6) then
                      pure <| .fail "invalid parsed Huffman group count"
                    else if metadata.huffman.selectors.isEmpty then
                      pure <| .fail "expected at least one selector"
                    else if metadata.huffman.codeLengths.length ≠ metadata.huffman.groupCount then
                      pure <| .fail "code-length table count does not match group count"
                    else if ¬ metadata.huffman.codeLengths.all (fun table => table.length = alphaSize) then
                      pure <| .fail "unexpected code-length table width"
                    else
                      pure .pass
  }

private def exactEmptyDecodeCase : TestCase :=
  { name := "exact empty stream decompresses"
  , run := do
      match ← loadFixture "empty_level1.bz2.hex" with
      | .error err => pure <| .fail s!"fixture error: {err}"
      | .ok archive =>
          match BZip2.decompressBz2? archive with
          | .error err => pure <| .fail s!"decode error: {err}"
          | .ok decoded =>
              if decoded = ByteArray.empty then
                pure .pass
              else
                pure <| .fail "empty exact stream decoded to non-empty output"
  }

private def exactBananaDecodeCase : TestCase :=
  { name := "exact banana fixture decompresses"
  , run := do
      match ← loadFixture "banana_level1.bz2.hex" with
      | .error err => pure <| .fail s!"fixture error: {err}"
      | .ok archive =>
          let expected := byteArrayOfList <| [98, 97, 110, 97, 110, 97, 10].map UInt8.ofNat
          match BZip2.decompressBz2? archive with
          | .error err => pure <| .fail s!"decode error: {err}"
          | .ok decoded =>
              if decoded = expected then
                pure .pass
              else
                pure <| .fail "decoded banana fixture does not match expected bytes"
  }

private def exactConcatenatedCase : TestCase :=
  { name := "exact concatenated streams decompress sequentially"
  , run := do
      match ← loadFixture "banana_level1.bz2.hex", ← loadFixture "banana_level1.bz2.hex" with
      | .ok first, .ok second =>
          let archive := appendByteArray first second
          let expectedOne := byteArrayOfList <| [98, 97, 110, 97, 110, 97, 10].map UInt8.ofNat
          let expected := appendByteArray expectedOne expectedOne
          match BZip2.decompressBz2? archive with
          | .error err => pure <| .fail s!"decode error: {err}"
          | .ok decoded =>
              if decoded = expected then
                pure .pass
              else
                pure <| .fail "concatenated exact streams decoded incorrectly"
      | .error err, _ => pure <| .fail s!"first fixture error: {err}"
      | _, .error err => pure <| .fail s!"second fixture error: {err}"
  }

private def exactCorruptBlockCrcCase : TestCase :=
  { name := "exact decoder rejects bad block crc"
  , run := do
      match ← loadFixture "banana_level1.bz2.hex" with
      | .error err => pure <| .fail s!"fixture error: {err}"
      | .ok archive =>
          let corrupted := replaceByteAt archive 10 0x00
          match BZip2.decompressBz2? corrupted with
          | .ok _ =>
              pure <| .fail "corrupted exact stream unexpectedly decoded successfully"
          | .error _ =>
              pure .pass
  }

private def exactEncoderSelfRoundtripCase : TestCase :=
  { name := "exact encoder self-roundtrips"
  , run := do
      let input := byteArrayOfList <|
        [0, 0, 0, 0, 0, 0, 255, 254, 13, 10, 97, 97, 97, 97, 98, 99, 120, 121, 122].map UInt8.ofNat
      match BZip2.compressBz2? input with
      | .error err => pure <| .fail s!"encode error: {err}"
      | .ok archive =>
          match BZip2.decompressBz2? archive with
          | .error err => pure <| .fail s!"decode error: {err}"
          | .ok decoded =>
              if decoded = input then
                pure .pass
              else
                pure <| .fail "exact encoder did not self-roundtrip"
  }

private def exactFastBWTMatchesReferenceCase : TestCase :=
  { name := "fast exact BWT matches reference BWT on small blocks"
  , run := do
      let samples : List (String × ByteArray) :=
        [ ("empty", ByteArray.empty)
        , ("one-byte", byteArrayOfList [0x61])
        , ("banana", "banana\n".toUTF8)
        , ("repeated", byteArrayOfList ((List.replicate 12 0x41).map UInt8.ofNat))
        , ("binary-mixed",
            byteArrayOfList ([0, 255, 0, 255, 1, 2, 3, 4, 5, 250, 251, 13, 10].map UInt8.ofNat))
        , ("periodic", "abcabcabcabc".toUTF8)
        ]
      let rec loop : List (String × ByteArray) → IO TestOutcome
        | [] => pure .pass
        | (label, input) :: rest =>
            let reference := transformBWTReference input
            let fast := transformBWT input
            if fast = reference then
              loop rest
            else
              pure <| .fail s!"BWT mismatch on sample {label}"
      loop samples
  }

private def exactEncoderSystemBzip2Case : TestCase :=
  { name := "system bzip2 validates and decompresses our exact output"
  , run := do
      let input := byteArrayOfList <|
        [0, 0, 0, 0, 0, 255, 255, 255, 1, 2, 3, 4, 65, 65, 65, 65, 65, 10, 200].map UInt8.ofNat
      let archivePath : System.FilePath := "tests/tmp_exact_encoder_output.bz2"
      let outputPath : System.FilePath := "tests/tmp_exact_encoder_output"
      try
        match BZip2.compressBz2? input with
        | .error err => pure <| .fail s!"encode error: {err}"
        | .ok archive =>
            IO.FS.writeBinFile archivePath archive
            match ← runSystemBzip2 #["-t", archivePath.toString] with
            | .error err => pure <| .fail s!"system test failed: {err}"
            | .ok _ =>
                match ← runSystemBzip2 #["-dkf", archivePath.toString] with
                | .error err => pure <| .fail s!"system decompress failed: {err}"
                | .ok _ =>
                    let decoded ← IO.FS.readBinFile outputPath
                    if decoded = input then
                      pure .pass
                    else
                      pure <| .fail "system bzip2 decoded bytes do not match the original input"
      finally
        removeIfExists archivePath
        removeIfExists outputPath
  }

private def exactDecoderReadsSystemBzip2Case : TestCase :=
  { name := "our exact decoder reads fresh system bzip2 output"
  , run := do
      let input := byteArrayOfList <|
        [42, 42, 42, 42, 42, 1, 2, 3, 4, 5, 255, 0, 13, 10, 65, 66, 67].map UInt8.ofNat
      let inputPath : System.FilePath := "tests/tmp_system_source.bin"
      let archivePath : System.FilePath := "tests/tmp_system_source.bin.bz2"
      try
        IO.FS.writeBinFile inputPath input
        match ← runSystemBzip2 #["-kf", inputPath.toString] with
        | .error err => pure <| .fail s!"system compress failed: {err}"
        | .ok _ =>
            let archive ← IO.FS.readBinFile archivePath
            match BZip2.decompressBz2? archive with
            | .error err => pure <| .fail s!"decode error: {err}"
            | .ok decoded =>
                if decoded = input then
                  pure .pass
                else
                  pure <| .fail "our exact decoder did not match the original system-compressed bytes"
      finally
        removeIfExists inputPath
        removeIfExists archivePath
  }

private def cases : List TestCase :=
  [ exactHeaderCase
  , exactBlockMetadataCase
  , exactEmptyDecodeCase
  , exactBananaDecodeCase
  , exactConcatenatedCase
  , exactCorruptBlockCrcCase
  , exactFastBWTMatchesReferenceCase
  , exactEncoderSelfRoundtripCase
  , exactEncoderSystemBzip2Case
  , exactDecoderReadsSystemBzip2Case
  ]

def main : IO Unit := do
  let summary ← runCases {} cases
  IO.println s!"\nSummary: {summary.passed} passed, {summary.failed} failed"
  if summary.failed ≠ 0 then
    throw <| IO.userError s!"{summary.failed} exact `.bz2` test(s) failed."
