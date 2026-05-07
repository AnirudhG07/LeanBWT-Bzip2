import Bzip2

set_option autoImplicit false

open Bzip2.Format.BZ2

structure Summary where
  passed : Nat := 0
  failed : Nat := 0
deriving Repr

inductive TestOutcome where
  | pass
  | fail (message : String)
deriving Repr

structure TestCase where
  name : String
  run : IO TestOutcome

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
  | [], acc => .ok <| ByteArray.mk acc.reverse.toArray
  | [_], _ => .error "Fixture hex has odd length."
  | hi :: lo :: rest, acc =>
      match hexValue? hi, hexValue? lo with
      | some hiVal, some loVal =>
          decodeHexAux rest (UInt8.ofNat (hiVal * 16 + loVal) :: acc)
      | _, _ => .error "Fixture hex contains a non-hex character."

private def loadFixture (name : String) : IO (Except String ByteArray) := do
  let path : System.FilePath := s!"tests/fixtures/bz2/{name}"
  let raw ← IO.FS.readFile path
  let hexChars := raw.toList.filter (fun c => hexValue? c |>.isSome)
  pure <| decodeHexAux hexChars []

private def byteArrayOfList (xs : List UInt8) : ByteArray :=
  ByteArray.mk xs.toArray

private def appendByteArray (left right : ByteArray) : ByteArray :=
  right.foldl ByteArray.push left

private def replaceByteAtAux : List UInt8 → Nat → UInt8 → List UInt8
  | [], _, _ => []
  | _ :: rest, 0, value => value :: rest
  | byte :: rest, index + 1, value => byte :: replaceByteAtAux rest index value

private def replaceByteAt (bytes : ByteArray) (index : Nat) (value : UInt8) : ByteArray :=
  byteArrayOfList <| replaceByteAtAux bytes.toList index value

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

private def cases : List TestCase :=
  [ exactHeaderCase
  , exactBlockMetadataCase
  , exactEmptyDecodeCase
  , exactBananaDecodeCase
  , exactConcatenatedCase
  , exactCorruptBlockCrcCase
  ]

private def runCase (summary : Summary) (tc : TestCase) : IO Summary := do
  match ← tc.run with
  | .pass =>
      IO.println s!"PASS {tc.name}"
      pure { summary with passed := summary.passed + 1 }
  | .fail message =>
      IO.println s!"FAIL {tc.name}: {message}"
      pure { summary with failed := summary.failed + 1 }

private def runCases : Summary → List TestCase → IO Summary
  | summary, [] => pure summary
  | summary, tc :: rest => do
      let summary' ← runCase summary tc
      runCases summary' rest

def main : IO Unit := do
  let summary ← runCases {} cases
  IO.println s!"\nSummary: {summary.passed} passed, {summary.failed} failed"
  if summary.failed ≠ 0 then
    throw <| IO.userError s!"{summary.failed} exact `.bz2` test(s) failed."
