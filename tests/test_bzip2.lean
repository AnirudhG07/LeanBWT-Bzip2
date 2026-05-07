import Bzip2
import Bzip2.Format.Binary

set_option autoImplicit false

structure Summary where
  passed : Nat := 0
  failed : Nat := 0
  skipped : Nat := 0
deriving Repr

inductive TestOutcome where
  | pass
  | fail (message : String)
  | skip (reason : String)
deriving Repr

structure TestCase where
  name : String
  run : IO TestOutcome

def byteArrayOfList (xs : List UInt8) : ByteArray :=
  xs.foldl ByteArray.push ByteArray.empty

private def hexValue? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then
    some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then
    some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then
    some (10 + c.toNat - 'A'.toNat)
  else
    none

private def decodeHexAux : List Char → List UInt8 → Except String ByteArray
  | [], acc => .ok <| byteArrayOfList acc.reverse
  | [_], _ => .error "Fixture hex has odd length."
  | hi :: lo :: rest, acc =>
      match hexValue? hi, hexValue? lo with
      | some hiVal, some loVal =>
          decodeHexAux rest (UInt8.ofNat (hiVal * 16 + loVal) :: acc)
      | _, _ => .error "Fixture hex contains a non-hex character."

private def loadExactFixture (name : String) : IO (Except String ByteArray) := do
  let path : System.FilePath := s!"tests/fixtures/bz2/{name}"
  let raw ← IO.FS.readFile path
  let hexChars := raw.toList.filter (fun c => hexValue? c |>.isSome)
  pure <| decodeHexAux hexChars []

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

private def exactLinuxFixtureCase : TestCase :=
  { name := "decode Linux-generated .bz2"
  , run := do
      match ← loadExactFixture "banana_level1.bz2.hex" with
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

private def pendingLargeCases : List TestCase :=
  [ pendingCase "multi-megabyte text"
      "Current proved matrix-based BWT is too slow for multi-megabyte execution; enable after native block sorter lands."
  , pendingCase "multi-megabyte binary"
      "Current proved matrix-based BWT is too slow for multi-megabyte execution; enable after native block sorter lands."
  , pendingCase "highly repetitive large file"
      "Activate after native block implementation replaces the spec-layer matrix algorithm."
  , pendingCase "incompressible large file"
      "Activate after native block implementation replaces the spec-layer matrix algorithm."
  , pendingCase "files spanning many large blocks"
      "Activate after native block implementation replaces the spec-layer matrix algorithm."
  ]

private def pendingExactBz2Cases : List TestCase :=
  [ pendingCase "malformed selector list rejects"
      "Requires the exact bz2 Huffman-selector decoder."
  , pendingCase "malformed code lengths rejects"
      "Requires the exact bz2 canonical Huffman length decoder."
  , pendingCase "missing end-of-block symbol rejects"
      "Requires the exact bz2 end-of-block symbol stream."
  , exactLinuxFixtureCase
  , pendingCase "Linux bzip2 validates our output"
      "Requires exact bz2 block encoding."
  ]

private def allCases : List TestCase :=
  smallCases ++ mediumCases ++ streamCases ++ negativeCases ++ pendingLargeCases ++ pendingExactBz2Cases

private def runCase (summary : Summary) (tc : TestCase) : IO Summary := do
  match ← tc.run with
  | .pass =>
      IO.println s!"PASS {tc.name}"
      pure { summary with passed := summary.passed + 1 }
  | .fail message =>
      IO.println s!"FAIL {tc.name}: {message}"
      pure { summary with failed := summary.failed + 1 }
  | .skip reason =>
      IO.println s!"SKIP {tc.name}: {reason}"
      pure { summary with skipped := summary.skipped + 1 }

private def runCases : Summary → List TestCase → IO Summary
  | summary, [] => pure summary
  | summary, tc :: rest => do
      let summary' ← runCase summary tc
      runCases summary' rest

def main : IO Unit := do
  let summary ← runCases {} allCases
  IO.println s!"\nSummary: {summary.passed} passed, {summary.failed} failed, {summary.skipped} skipped"
  if summary.failed ≠ 0 then
    throw <| IO.userError s!"{summary.failed} test(s) failed."
