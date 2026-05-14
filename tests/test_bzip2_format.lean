import Bzip2
import Bzip2.Format.Binary
import Bzip2.Format.BZ2.BitWriter
import Bzip2.Format.BZ2.CRC
import Bzip2.Format.BZ2.Canonical
import Bzip2.Format.BZ2.Model
import Bzip2.Format.BZ2.Transform
import tests.test_bzip2

set_option autoImplicit false

private def runLocalSystemBzip2 (args : Array String) : IO (Except String Unit) := do
  let out ← IO.Process.output { cmd := "bzip2", args := args }
  if out.exitCode = 0 then
    pure (.ok ())
  else
    pure (.error s!"exit {out.exitCode}: {out.stderr}")

private def runLocalSystemBunzip2 (args : Array String) : IO (Except String Unit) := do
  let out ← IO.Process.output { cmd := "bunzip2", args := args }
  if out.exitCode = 0 then
    pure (.ok ())
  else
    pure (.error s!"exit {out.exitCode}: {out.stderr}")

private def bumpByte (b : UInt8) : UInt8 :=
  UInt8.ofNat (b.toNat + 1)

private def overwriteAt : Nat → (UInt8 → UInt8) → List UInt8 → List UInt8
  | _, _, [] => []
  | 0, f, b :: bs => f b :: bs
  | n + 1, f, b :: bs => b :: overwriteAt n f bs

private def appendBytes (bytes suffix : ByteArray) : ByteArray :=
  byteArrayOfList (bytes.toList ++ suffix.toList)

private def truncateLast (bytes : ByteArray) : ByteArray :=
  byteArrayOfList <| bytes.toList.take (bytes.size - 1)

private def corruptAt (index : Nat) (bytes : ByteArray) : ByteArray :=
  byteArrayOfList <| overwriteAt index bumpByte bytes.toList

private def nextSeed (seed : Nat) : Nat :=
  (1664525 * seed + 1013904223) % 4294967296

private def pseudoRandomBytesAux : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, seed =>
      let seed' := nextSeed seed
      UInt8.ofNat seed' :: pseudoRandomBytesAux n seed'

private def pseudoRandomBytes (seed len : Nat) : ByteArray :=
  byteArrayOfList (pseudoRandomBytesAux len seed)

private def repeatedByte (count : Nat) (value : UInt8) : ByteArray :=
  byteArrayOfList (List.replicate count value)

private def allByteValuesOnce : ByteArray :=
  byteArrayOfList ((List.range 256).map UInt8.ofNat)

private def allByteValuesRepeated (times : Nat) : ByteArray :=
  byteArrayOfList <|
    (List.range times).foldr
      (fun _ acc => ((List.range 256).map UInt8.ofNat) ++ acc)
      []

private def repetitiveBinary : ByteArray :=
  byteArrayOfList <|
    List.replicate 96 0x00
    ++ List.replicate 96 0xFF
    ++ List.replicate 96 0x00
    ++ List.replicate 96 0x7E

private def alternatingBinary : ByteArray :=
  byteArrayOfList <|
    (List.range 128).map (fun i => if i % 2 = 0 then (0x00 : UInt8) else 0xFF)

private def mediumEnglish : ByteArray :=
  ("The quick brown fox jumps over the lazy dog.\nBWT makes nearby contexts line up.\n").toUTF8

private def sourceCodeSnippet : ByteArray :=
  "def fib : Nat -> Nat\n| 0 => 0\n| 1 => 1\n| n + 2 => fib (n + 1) + fib n\n".toUTF8

private def jsonSnippet : ByteArray :=
  "{\"name\":\"lean-bzip2\",\"ok\":true,\"items\":[1,2,3,4],\"meta\":{\"stage\":\"tests\"}}\n".toUTF8

private def blockBoundaryData : ByteArray :=
  byteArrayOfList <| (List.range 97).map (fun i => UInt8.ofNat (i % 251))

private def roundtripArchive (archive : ByteArray) (expected : ByteArray) : TestOutcome :=
  match decompressBinary? archive with
  | .error err => .fail s!"decompression error: {err}"
  | .ok output =>
      if output == expected then
        .pass
      else
        .fail "roundtrip mismatch"

private def roundtripCase (name : String) (input : ByteArray) : TestCase :=
  { name := name
  , run := do
      match compressBinary? input with
      | .error err => pure <| .fail s!"compression error: {err}"
      | .ok archive => pure <| roundtripArchive archive input
  }

private def roundtripWithConfigCase (name : String)
    (config : Bzip2.Format.StreamConfig) (input : ByteArray) : TestCase :=
  { name := name
  , run := do
      match Bzip2.Format.compressBinaryWithConfig? config input with
      | .error err => pure <| .fail s!"compression error: {err}"
      | .ok archive => pure <| roundtripArchive archive input
  }

private def rejectionCase (name : String) (archiveThunk : IO (Except String ByteArray)) : TestCase :=
  { name := name
  , run := do
      match ← archiveThunk with
      | .error err => pure <| .fail s!"setup error: {err}"
      | .ok archive =>
          match decompressBinary? archive with
          | .ok _ => pure <| .fail "damaged archive unexpectedly decoded"
          | .error _ => pure .pass
  }

private def exactRejectionCase (name : String) (archiveThunk : IO (Except String ByteArray)) : TestCase :=
  { name := name
  , run := do
      match ← archiveThunk with
      | .error err => pure <| .fail s!"setup error: {err}"
      | .ok archive =>
          match decompressBz2? archive with
          | .ok _ => pure <| .fail "damaged exact archive unexpectedly decoded"
          | .error _ => pure .pass
  }

private def pendingCase (name reason : String) : TestCase :=
  { name := name
  , run := pure (.skip reason)
  }

private def fileRoundtripCase : TestCase :=
  { name := "file roundtrip"
  , run := do
      let input := "The quick brown fox jumps over the lazy dog"
      let testFile : System.FilePath := "test_file.txt"
      let defaultCompressed : System.FilePath := "test_file.txt.lbz2"
      let defaultOutput : System.FilePath := "test_file_out.txt"
      IO.FS.writeFile testFile input
      try
        let compressedFile ← compressFile testFile
        let decompressedFile ← decompressFile compressedFile (some defaultOutput)
        let decompressedText ← IO.FS.readFile decompressedFile
        IO.FS.removeFile testFile
        IO.FS.removeFile compressedFile
        IO.FS.removeFile decompressedFile
        if decompressedText = input then
          pure .pass
        else
          pure <| .fail "file contents mismatch"
      catch e =>
        if (← testFile.pathExists) then
          IO.FS.removeFile testFile
        if (← defaultCompressed.pathExists) then
          IO.FS.removeFile defaultCompressed
        if (← defaultOutput.pathExists) then
          IO.FS.removeFile defaultOutput
        pure <| .fail s!"IO error: {e.toString}"
  }

private def exactFileInteropCase : TestCase :=
  { name := "exact bz2 file helpers interoperate"
  , run := do
      let input := "Exact file helper roundtrip.\nAAAABBBBCCCCDDDDEEEE\n"
      let inputPath : System.FilePath := "test_exact_file.txt"
      let defaultCompressed : System.FilePath := "test_exact_file.txt.bz2"
      let defaultOutput : System.FilePath := "test_exact_file_out.txt"
      IO.FS.writeFile inputPath input
      try
        let compressedFile ← compressBz2File inputPath
        match ← runLocalSystemBzip2 #["-t", compressedFile.toString] with
        | .error err => pure <| .fail s!"system test failed: {err}"
        | .ok _ =>
            let decompressedFile ← decompressBz2File compressedFile (some defaultOutput)
            let decompressedText ← IO.FS.readFile decompressedFile
            IO.FS.removeFile inputPath
            IO.FS.removeFile compressedFile
            IO.FS.removeFile decompressedFile
            if decompressedText = input then
              pure .pass
            else
              pure <| .fail "exact file helper contents mismatch"
      catch e =>
        if (← inputPath.pathExists) then
          IO.FS.removeFile inputPath
        if (← defaultCompressed.pathExists) then
          IO.FS.removeFile defaultCompressed
        if (← defaultOutput.pathExists) then
          IO.FS.removeFile defaultOutput
        pure <| .fail s!"IO error: {e.toString}"
  }

private def concatenatedStreamCase : TestCase :=
  { name := "concatenated stream roundtrip"
  , run := do
      let left := "left stream".toUTF8
      let right := "right stream".toUTF8
      match compressBinary? left, compressBinary? right with
      | .ok leftArchive, .ok rightArchive =>
          let concatenated := byteArrayOfList (leftArchive.toList ++ rightArchive.toList)
          let expected := byteArrayOfList (left.toList ++ right.toList)
          pure <| roundtripArchive concatenated expected
      | .error err, _ => pure <| .fail s!"left compression error: {err}"
      | _, .error err => pure <| .fail s!"right compression error: {err}"
  }

private def badMagicCase : TestCase :=
  rejectionCase "bad magic rejects" do
    let archive := compressBinary? "bad magic".toUTF8
    pure <| archive.map (corruptAt 0)

private def badBlockCrcCase : TestCase :=
  rejectionCase "bad block CRC rejects" do
    let archive := compressBinary? "block crc".toUTF8
    pure <| archive.map (corruptAt 10)

private def badStreamCrcCase : TestCase :=
  rejectionCase "bad stream CRC rejects" do
    let archive := compressBinary? "stream crc".toUTF8
    pure <| archive.map (fun bytes => corruptAt (bytes.size - 1) bytes)

private def badPayloadCase : TestCase :=
  rejectionCase "damaged block payload rejects" do
    let archive := compressBinary? "payload corruption should fail".toUTF8
    pure <| archive.map (corruptAt 22)

private def truncatedStreamCase : TestCase :=
  rejectionCase "truncated stream rejects" do
    let archive := compressBinary? "truncated".toUTF8
    pure <| archive.map truncateLast

private def trailingGarbageCase : TestCase :=
  rejectionCase "trailing garbage rejects" do
    let archive := compressBinary? "garbage".toUTF8
    pure <| archive.map (fun bytes => appendBytes bytes (byteArrayOfList [0x00, 0x01]))

private def damagedSecondStreamCase : TestCase :=
  rejectionCase "concatenated stream with damaged second stream rejects" do
    match compressBinary? "left".toUTF8, compressBinary? "right".toUTF8 with
    | .ok leftArchive, .ok rightArchive =>
        let brokenRight := corruptAt 10 rightArchive
        pure <| .ok <| byteArrayOfList (leftArchive.toList ++ brokenRight.toList)
    | .error err, _ => pure (.error s!"left compression error: {err}")
    | _, .error err => pure (.error s!"right compression error: {err}")

private def exactBitMaskAt (index : Nat) : Nat :=
  2 ^ (15 - index)

private def exactGroupMask (group : Nat) (usedBytes : List UInt8) : Nat :=
  (List.range 16).foldl
    (fun acc offset =>
      if UInt8.ofNat (group * 16 + offset) ∈ usedBytes then
        acc + exactBitMaskAt offset
      else
        acc)
    0

private def exactGroupsBitmap (usedBytes : List UInt8) : Nat :=
  (List.range 16).foldl
    (fun acc group =>
      if exactGroupMask group usedBytes = 0 then
        acc
      else
        acc + exactBitMaskAt group)
    0

private def exactWriteUsedBytes (writer : Bzip2.Format.BZ2.BitWriter) (usedBytes : List UInt8) :
    Bzip2.Format.BZ2.BitWriter :=
  let writer := writer.writeBits 16 (exactGroupsBitmap usedBytes)
  (List.range 16).foldl
    (fun writer group =>
      let mask := exactGroupMask group usedBytes
      if mask = 0 then writer else writer.writeBits 16 mask)
    writer

private def exactWriteUnaryZeroTerminated
    (writer : Bzip2.Format.BZ2.BitWriter) (count : Nat) :
    Bzip2.Format.BZ2.BitWriter :=
  (writer.writeRepeatedBit count true).writeBit false

private def exactMinBitsForCount (count : Nat) : Nat :=
  Id.run do
    let mut bits := 0
    while 2 ^ bits < count do
      bits := bits + 1
    pure bits

private def uniformCodeLengths (alphaSize : Nat) : List Nat :=
  List.replicate alphaSize (max 1 (exactMinBitsForCount alphaSize))

private def exactWriteCodeLengthTable
    (writer : Bzip2.Format.BZ2.BitWriter) (lengths : List Nat) :
    Bzip2.Format.BZ2.BitWriter :=
  Id.run do
    let startLength := lengths.headD 0
    let mut writer := writer.writeBits 5 startLength
    let mut current := startLength
    for target in lengths do
      while current ≠ target do
        writer := writer.writeBit true
        if target < current then
          writer := writer.writeBit true
          current := current - 1
        else
          writer := writer.writeBit false
          current := current + 1
      writer := writer.writeBit false
    pure writer

private def exactWriteSymbolStream
    (writer : Bzip2.Format.BZ2.BitWriter)
    (table : Bzip2.Format.BZ2.CanonicalTable)
    (symbols : List Nat) :
    Except String Bzip2.Format.BZ2.BitWriter := do
  symbols.foldlM
    (fun writer symbol => do
      let some entry := table.findEntry? symbol
        | throw "Malformed exact-test builder lost a canonical Huffman symbol."
      pure (writer.writeBits entry.bitLength entry.code))
    writer

private def exactEntropyInputOf (input : ByteArray) :
    Except String Bzip2.Format.BZ2.EntropyInput := do
  let blocks ← Bzip2.Format.BZ2.prepareBlocks 100000 input
  match blocks with
  | [block] => pure (Bzip2.Format.BZ2.prepareEntropyInput block)
  | [] => throw "Malformed exact-test builder expected one non-empty block."
  | _ => throw "Malformed exact-test builder expected a single exact block."

private def exactArchivePrefix (entropy : Bzip2.Format.BZ2.EntropyInput) :
    Bzip2.Format.BZ2.BitWriter × UInt32 :=
  let blockCRC := Bzip2.Format.BZ2.crc32 entropy.original
  let writer := Bzip2.Format.BZ2.BitWriter.empty
  let writer := writer.writeBits 8 0x42
  let writer := writer.writeBits 8 0x5A
  let writer := writer.writeBits 8 0x68
  let writer := writer.writeBits 8 49
  let writer := writer.writeBits 48 Bzip2.Format.BZ2.blockMagic
  let writer := writer.writeBits 32 blockCRC.toNat
  let writer := writer.writeBit false
  let writer := writer.writeBits 24 entropy.origPtr
  let writer := exactWriteUsedBytes writer entropy.usedBytes
  (writer, blockCRC)

private def malformedSelectorArchive? : Except String ByteArray := do
  let entropy ← exactEntropyInputOf "selector bug\n".toUTF8
  let (writer, _) := exactArchivePrefix entropy
  let writer := writer.writeBits 3 2
  let writer := writer.writeBits 15 1
  let writer := writer.writeBit true
  let writer := writer.writeBit true
  let writer := writer.writeBit false
  pure writer.toByteArray

private def malformedCodeLengthsArchive? : Except String ByteArray := do
  let entropy ← exactEntropyInputOf "code lengths bug\n".toUTF8
  let (writer, _) := exactArchivePrefix entropy
  let writer := writer.writeBits 3 2
  let writer := writer.writeBits 15 1
  let writer := exactWriteUnaryZeroTerminated writer 0
  let writer := writer.writeBits 5 21
  pure writer.toByteArray

private def missingEndOfBlockArchive? : Except String ByteArray := do
  let entropy ← exactEntropyInputOf "missing eob\n".toUTF8
  let alphaSize := entropy.usedBytes.length + 2
  let lengths := uniformCodeLengths alphaSize
  let canonical ← Bzip2.Format.BZ2.CanonicalTable.build lengths
  let (writer, blockCRC) := exactArchivePrefix entropy
  let writer := writer.writeBits 3 2
  let writer := writer.writeBits 15 1
  let writer := exactWriteUnaryZeroTerminated writer 0
  let writer := exactWriteCodeLengthTable writer lengths
  let writer := exactWriteCodeLengthTable writer lengths
  let symbolsWithoutEob := entropy.symbols.take (entropy.symbols.length - 1)
  let writer ← exactWriteSymbolStream writer canonical symbolsWithoutEob
  let streamCRC := Bzip2.Format.BZ2.combineStreamCRC 0 blockCRC
  let writer := writer.writeBits 48 Bzip2.Format.BZ2.endMagic
  let writer := writer.writeBits 32 streamCRC.toNat
  pure writer.toByteArray

private def malformedSelectorListCase : TestCase :=
  exactRejectionCase "malformed selector list rejects" do
    pure malformedSelectorArchive?

private def malformedCodeLengthsCase : TestCase :=
  exactRejectionCase "malformed code lengths rejects" do
    pure malformedCodeLengthsArchive?

private def missingEndOfBlockCase : TestCase :=
  exactRejectionCase "missing end-of-block symbol rejects" do
    pure missingEndOfBlockArchive?

private def exactLinuxFixtureCase : TestCase :=
  { name := "decode Linux-generated .bz2"
  , run := do
      match ← loadFixture "banana_level1.bz2.hex" with
      | .error err => pure <| .fail s!"fixture error: {err}"
      | .ok archive =>
          let expected := "banana\n".toUTF8
          match decompressBz2? archive with
          | .error err => pure <| .fail s!"exact decode error: {err}"
          | .ok decoded =>
              if decoded = expected then
                pure .pass
              else
                pure <| .fail "exact `.bz2` fixture decoded incorrectly"
  }

private def exactLinuxValidationCase : TestCase :=
  { name := "Linux bzip2 validates our output"
  , run := do
      let input := "Exact bz2 interoperability check.\nAAAAAABBBBBCCCCCDDDD\n".toUTF8
      let archivePath : System.FilePath := "tests/tmp_main_exact_output.bz2"
      let outputPath : System.FilePath := "tests/tmp_main_exact_output"
      try
        match compressBz2? input with
        | .error err => pure <| .fail s!"exact encode error: {err}"
        | .ok archive =>
            IO.FS.writeBinFile archivePath archive
            match ← runLocalSystemBzip2 #["-t", archivePath.toString] with
            | .error err => pure <| .fail s!"system test failed: {err}"
            | .ok _ =>
                match ← runLocalSystemBzip2 #["-dkf", archivePath.toString] with
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

private def exactBunzip2ValidationCase : TestCase :=
  { name := "Linux bunzip2 decompresses our output"
  , run := do
      let input := "bunzip2 compatibility check\n0000111122223333\n".toUTF8
      let archivePath : System.FilePath := "tests/tmp_main_bunzip2_output.bz2"
      let outputPath : System.FilePath := "tests/tmp_main_bunzip2_output"
      try
        match compressBz2? input with
        | .error err => pure <| .fail s!"exact encode error: {err}"
        | .ok archive =>
            IO.FS.writeBinFile archivePath archive
            match ← runLocalSystemBunzip2 #["-kf", archivePath.toString] with
            | .error err => pure <| .fail s!"system bunzip2 failed: {err}"
            | .ok _ =>
                let decoded ← IO.FS.readBinFile outputPath
                if decoded = input then
                  pure .pass
                else
                  pure <| .fail "system bunzip2 decoded bytes do not match the original input"
      finally
        removeIfExists archivePath
        removeIfExists outputPath
  }

private def exactInteropCorpus : List (Nat × String × ByteArray) :=
  [ (0, "text", mediumEnglish)
  , (1, "repetitive-binary", repetitiveBinary)
  , (2, "pseudo-random", pseudoRandomBytes 2026 96)
  ]

private def exactBlockSizeDigits : List Nat :=
  (List.range 9).map (· + 1)

private def foldChecks {α : Type} (items : List α) (f : α → IO (Except String Unit)) :
    IO (Except String Unit) := do
  match items with
  | [] => pure (.ok ())
  | item :: rest =>
      match ← f item with
      | .error err => pure (.error err)
      | .ok _ => foldChecks rest f

private def checkSystemDecodesOurExactArchive
    (digit index : Nat) (label : String) (input : ByteArray) :
    IO (Except String Unit) := do
  let archivePath : System.FilePath := s!"tests/tmp_exact_phase3_ours_{digit}_{index}_{label}.bz2"
  let outputPath : System.FilePath := s!"tests/tmp_exact_phase3_ours_{digit}_{index}_{label}"
  try
    match compressBz2WithBlockSize? digit input with
    | .error err => pure (.error s!"exact encode error for block size -{digit} ({label}): {err}")
    | .ok archive =>
        IO.FS.writeBinFile archivePath archive
        match ← runLocalSystemBzip2 #["-t", archivePath.toString] with
        | .error err =>
            pure (.error s!"system bzip2 -t failed for block size -{digit} ({label}): {err}")
        | .ok _ =>
            match ← runLocalSystemBunzip2 #["-kf", archivePath.toString] with
            | .error err =>
                pure (.error s!"system bunzip2 failed for block size -{digit} ({label}): {err}")
            | .ok _ =>
                let decoded ← IO.FS.readBinFile outputPath
                if decoded = input then
                  pure (.ok ())
                else
                  pure (.error s!"system decode mismatch for block size -{digit} ({label})")
  finally
    removeIfExists archivePath
    removeIfExists outputPath

private def checkOurDecoderReadsSystemArchive
    (digit index : Nat) (label : String) (input : ByteArray) :
    IO (Except String Unit) := do
  let inputPath : System.FilePath := s!"tests/tmp_exact_phase3_system_{digit}_{index}_{label}.bin"
  let archivePath : System.FilePath := s!"tests/tmp_exact_phase3_system_{digit}_{index}_{label}.bin.bz2"
  try
    IO.FS.writeBinFile inputPath input
    match ← runLocalSystemBzip2 #[s!"-{digit}", "-kf", inputPath.toString] with
    | .error err =>
        pure (.error s!"system compress failed for block size -{digit} ({label}): {err}")
    | .ok _ =>
        let archive ← IO.FS.readBinFile archivePath
        match decompressBz2? archive with
        | .error err =>
            pure (.error s!"exact decoder failed on system block size -{digit} ({label}): {err}")
        | .ok decoded =>
            if decoded = input then
              pure (.ok ())
            else
              pure (.error s!"exact decoder mismatch for system block size -{digit} ({label})")
  finally
    removeIfExists inputPath
    removeIfExists archivePath

private def exactConcatenatedInteropCase : TestCase :=
  { name := "exact concatenated streams interoperate both ways"
  , run := do
      let left := "left exact concatenated stream\nAAAAABBBBB\n".toUTF8
      let right := byteArrayOfList <|
        [0, 255, 0, 255, 1, 2, 3, 4, 5, 6, 200, 201, 202].map UInt8.ofNat
      let expected := appendBytes left right
      let ourArchivePath : System.FilePath := "tests/tmp_phase3_concat_ours.bz2"
      let ourOutputPath : System.FilePath := "tests/tmp_phase3_concat_ours"
      let sysLeftPath : System.FilePath := "tests/tmp_phase3_concat_left.bin"
      let sysLeftArchivePath : System.FilePath := "tests/tmp_phase3_concat_left.bin.bz2"
      let sysRightPath : System.FilePath := "tests/tmp_phase3_concat_right.bin"
      let sysRightArchivePath : System.FilePath := "tests/tmp_phase3_concat_right.bin.bz2"
      try
        match compressBz2WithBlockSize? 1 left, compressBz2WithBlockSize? 9 right with
        | .ok leftArchive, .ok rightArchive =>
            IO.FS.writeBinFile ourArchivePath (appendBytes leftArchive rightArchive)
            match ← runLocalSystemBunzip2 #["-kf", ourArchivePath.toString] with
            | .error err => pure <| .fail s!"system bunzip2 failed on concatenated exact stream: {err}"
            | .ok _ =>
                let systemDecoded ← IO.FS.readBinFile ourOutputPath
                if systemDecoded ≠ expected then
                  pure <| .fail "system bunzip2 did not reproduce concatenated exact payload"
                else
                  IO.FS.writeBinFile sysLeftPath left
                  IO.FS.writeBinFile sysRightPath right
                  match ← runLocalSystemBzip2 #["-1", "-kf", sysLeftPath.toString] with
                  | .error err => pure <| .fail s!"system compress failed for left concatenated source: {err}"
                  | .ok _ =>
                      match ← runLocalSystemBzip2 #["-9", "-kf", sysRightPath.toString] with
                      | .error err => pure <| .fail s!"system compress failed for right concatenated source: {err}"
                      | .ok _ =>
                          let sysLeftArchive ← IO.FS.readBinFile sysLeftArchivePath
                          let sysRightArchive ← IO.FS.readBinFile sysRightArchivePath
                          match decompressBz2? (appendBytes sysLeftArchive sysRightArchive) with
                          | .error err => pure <| .fail s!"exact decoder failed on concatenated system streams: {err}"
                          | .ok decoded =>
                              if decoded = expected then
                                pure .pass
                              else
                                pure <| .fail "exact decoder did not reproduce concatenated system payload"
        | .error err, _ => pure <| .fail s!"exact encode error for left concatenated stream: {err}"
        | _, .error err => pure <| .fail s!"exact encode error for right concatenated stream: {err}"
      finally
        removeIfExists ourArchivePath
        removeIfExists ourOutputPath
        removeIfExists sysLeftPath
        removeIfExists sysLeftArchivePath
        removeIfExists sysRightPath
        removeIfExists sysRightArchivePath
  }

private def exactAllBlockSizesInteropCase : TestCase :=
  { name := "exact bz2 mixed corpus interoperates across block sizes 1-9"
  , run := do
      match ← foldChecks exactBlockSizeDigits (fun digit =>
        foldChecks exactInteropCorpus (fun entry => do
          let index := entry.1
          let label := entry.2.1
          let input := entry.2.2
          match ← checkSystemDecodesOurExactArchive digit index label input with
          | .error err => pure (.error err)
          | .ok _ => checkOurDecoderReadsSystemArchive digit index label input)) with
      | .ok _ => pure .pass
      | .error err => pure <| .fail err
  }

private def smallCases : List TestCase :=
  [ roundtripCase "empty bytes" ByteArray.empty
  , roundtripCase "one byte" (byteArrayOfList [0x41])
  , roundtripCase "two bytes" (byteArrayOfList [0x41, 0x42])
  , roundtripCase "three bytes" (byteArrayOfList [0x41, 0x42, 0x43])
  , roundtripCase "four equal bytes" (repeatedByte 4 0x61)
  , roundtripCase "five equal bytes" (repeatedByte 5 0x61)
  , roundtripCase "alternating bytes" alternatingBinary
  , roundtripCase "all 256 byte values once" allByteValuesOnce
  , roundtripCase "all 256 byte values repeated" (allByteValuesRepeated 2)
  ]

private def mediumCases : List TestCase :=
  [ roundtripCase "short English text" mediumEnglish
  , roundtripCase "source code snippet" sourceCodeSnippet
  , roundtripCase "JSON snippet" jsonSnippet
  , roundtripCase "repetitive binary" repetitiveBinary
  , roundtripCase "pseudo-random binary" (pseudoRandomBytes 12345 256)
  , roundtripWithConfigCase "crosses one block boundary"
      { blockSizeDigit := 1, blockBytes := 32 } blockBoundaryData
  ]

private def streamCases : List TestCase :=
  [ roundtripCase "binary roundtrip smoke" "The quick brown fox jumps over the lazy dog".toUTF8
  , concatenatedStreamCase
  , roundtripWithConfigCase "multi-block roundtrip"
      { blockSizeDigit := 1, blockBytes := 32 } (pseudoRandomBytes 7 192)
  , fileRoundtripCase
  , exactFileInteropCase
  ]

private def negativeCases : List TestCase :=
  [ badMagicCase
  , badBlockCrcCase
  , badStreamCrcCase
  , badPayloadCase
  , truncatedStreamCase
  , trailingGarbageCase
  , damagedSecondStreamCase
  ]

private def exactBz2Cases : List TestCase :=
  [ malformedSelectorListCase
  , malformedCodeLengthsCase
  , missingEndOfBlockCase
  , exactLinuxFixtureCase
  , exactLinuxValidationCase
  , exactBunzip2ValidationCase
  , exactConcatenatedInteropCase
  , exactAllBlockSizesInteropCase
  ]

private def allCases : List TestCase :=
  smallCases ++ mediumCases ++ streamCases ++ negativeCases ++ exactBz2Cases

def main : IO Unit := do
  let summary ← runCases {} allCases
  IO.println s!"\nSummary: {summary.passed} passed, {summary.failed} failed, {summary.skipped} skipped"
  if summary.failed ≠ 0 then
    throw <| IO.userError s!"{summary.failed} test(s) failed."
