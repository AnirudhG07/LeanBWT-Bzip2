import Bzip2.Format.BZ2.BitReader
import Bzip2.Format.BZ2.Model

/-!
Exact `.bz2` metadata parser.

This phase-1 parser intentionally stops after the Huffman metadata for a block.
It does not yet decode the block contents themselves.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

private def bitSetFromLeft (width value index : Nat) : Bool :=
  ((value / (2 ^ (width - 1 - index))) % 2 = 1)

/-- Parse the exact `BZh<digit>` stream header. -/
def parseStreamHeader (reader : BitReader) : Except String (StreamHeader × BitReader) := do
  let (b, reader1) ← reader.readBits 8
  let (z, reader2) ← reader1.readBits 8
  let (h, reader3) ← reader2.readBits 8
  let (digit, reader4) ← reader3.readBits 8
  if b ≠ 0x42 ∨ z ≠ 0x5A ∨ h ≠ 0x68 then
    throw "Invalid `.bz2` stream header."
  if 49 ≤ digit ∧ digit ≤ 57 then
    let blockSizeDigit := digit - 48
    pure ({ blockSizeDigit := blockSizeDigit, blockSizeBytes := blockSizeDigit * 100000 }, reader4)
  else
    throw "Invalid `.bz2` block size digit."

/-- Parse the next 48-bit section marker. -/
def parseSectionMarker (reader : BitReader) : Except String (SectionMarker × BitReader) := do
  let (marker, reader') ← reader.readBits 48
  if marker = blockMagic then
    pure (.block, reader')
  else if marker = endMagic then
    pure (.eos, reader')
  else
    throw "Invalid `.bz2` section marker."

private def parseUsedBytesAux :
    Nat → Nat → Nat → BitReader → List UInt8 → Except String (List UInt8 × BitReader)
  | 0, _, _, reader, acc => pure (acc, reader)
  | fuel + 1, group, groupsBitmap, reader, acc =>
      if bitSetFromLeft 16 groupsBitmap group then do
        let (groupBitmap, reader') ← reader.readBits 16
        let groupBytes :=
          (List.range 16).filterMap (fun offset =>
            if bitSetFromLeft 16 groupBitmap offset then
              some (UInt8.ofNat (group * 16 + offset))
            else
              none)
        parseUsedBytesAux fuel (group + 1) groupsBitmap reader' (acc ++ groupBytes)
      else
        parseUsedBytesAux fuel (group + 1) groupsBitmap reader acc

/-- Parse the exact bzip2 used-byte bitmap and reconstruct the byte alphabet. -/
def parseUsedBytes (reader : BitReader) : Except String (List UInt8 × BitReader) := do
  let (groupsBitmap, reader') ← reader.readBits 16
  parseUsedBytesAux 16 0 groupsBitmap reader' []

/-- Parse a compressed block header after its 48-bit magic. -/
def parseBlockHeaderAfterMagic (reader : BitReader) : Except String (BlockHeader × BitReader) := do
  let (blockCRC, reader1) ← reader.readBits 32
  let (randomised, reader2) ← reader1.readBit
  let (origPtr, reader3) ← reader2.readBits 24
  let (usedBytes, reader4) ← parseUsedBytes reader3
  pure
    ( { blockCRC := UInt32.ofNat blockCRC
      , randomised := randomised
      , origPtr := origPtr
      , usedBytes := usedBytes
      }
    , reader4
    )

private def moveToFrontIndex (index : Nat) (xs : List Nat) : Except String (Nat × List Nat) :=
  match xs[index]? with
  | none => .error "Selector index is outside the Huffman-group range."
  | some value => .ok (value, value :: xs.erase value)

private def parseUnaryIndexAux :
    Nat → Nat → BitReader → Except String (Nat × BitReader)
  | 0, _, _ => .error "Unary selector encoding did not terminate."
  | fuel + 1, acc, reader => do
      let (bit, reader') ← reader.readBit
      if bit then
        parseUnaryIndexAux fuel (acc + 1) reader'
      else
        pure (acc, reader')

private def parseUnaryIndex (reader : BitReader) : Except String (Nat × BitReader) :=
  parseUnaryIndexAux 64 0 reader

private def parseSelectorsAux :
    Nat → Nat → BitReader → List Nat → List Nat → Except String (List Nat × BitReader)
  | 0, _, reader, _, acc => pure (acc.reverse, reader)
  | count + 1, groupCount, reader, mtf, acc => do
      let (encodedIndex, reader1) ← parseUnaryIndex reader
      if encodedIndex ≥ groupCount then
        throw "Encoded selector index exceeds the number of Huffman groups."
      let (selector, mtf') ← moveToFrontIndex encodedIndex mtf
      parseSelectorsAux count groupCount reader1 mtf' (selector :: acc)

private def adjustCodeLength (current : Nat) (decrement : Bool) : Except String Nat := do
  if decrement then
    if current = 0 then
      throw "Huffman code length underflow."
    else
      pure (current - 1)
  else if current = 20 then
    throw "Huffman code length overflow."
  else
    pure (current + 1)

private def parseOneLengthAux :
    Nat → Nat → BitReader → Except String (Nat × BitReader)
  | 0, _, _ => .error "Huffman code-length delta sequence did not terminate."
  | fuel + 1, current, reader => do
      let (continueBit, reader1) ← reader.readBit
      if continueBit then
        let (decrement, reader2) ← reader1.readBit
        let current' ← adjustCodeLength current decrement
        parseOneLengthAux fuel current' reader2
      else
        pure (current, reader1)

private def parseTableCodeLengthsAux :
    Nat → Nat → BitReader → List Nat → Except String (List Nat × BitReader)
  | 0, _, reader, acc => pure (acc.reverse, reader)
  | symCount + 1, current, reader, acc => do
      let (current', reader') ← parseOneLengthAux 64 current reader
      parseTableCodeLengthsAux symCount current' reader' (current' :: acc)

private def parseTableCodeLengths (alphaSize : Nat) (reader : BitReader) :
    Except String (List Nat × BitReader) := do
  let (startLength, reader1) ← reader.readBits 5
  if startLength > 20 then
    throw "Initial Huffman code length exceeds the `.bz2` limit."
  parseTableCodeLengthsAux alphaSize startLength reader1 []

private def parseCodeLengthTablesAux :
    Nat → Nat → BitReader → List (List Nat) → Except String (List (List Nat) × BitReader)
  | 0, _, reader, acc => pure (acc.reverse, reader)
  | groupCount + 1, alphaSize, reader, acc => do
      let (table, reader') ← parseTableCodeLengths alphaSize reader
      parseCodeLengthTablesAux groupCount alphaSize reader' (table :: acc)

/-- Parse exact `.bz2` Huffman metadata for a block. -/
def parseHuffmanMetadata (header : BlockHeader) (reader : BitReader) :
    Except String (HuffmanMetadata × BitReader) := do
  let (groupCount, reader1) ← reader.readBits 3
  if ¬ (2 ≤ groupCount ∧ groupCount ≤ 6) then
    throw "Invalid number of Huffman groups in `.bz2` block."
  let (selectorCount, reader2) ← reader1.readBits 15
  if selectorCount = 0 then
    throw "`.bz2` block must contain at least one selector."
  let (selectors, reader3) ← parseSelectorsAux selectorCount groupCount reader2 (List.range groupCount) []
  let (codeLengths, reader4) ← parseCodeLengthTablesAux groupCount header.alphaSize reader3 []
  pure
    ( { groupCount := groupCount
      , selectors := selectors
      , codeLengths := codeLengths
      }
    , reader4
    )

/-- Parse a compressed block section after its marker. -/
def parseBlockSectionAfterMarker (reader : BitReader) : Except String (BlockMetadata × BitReader) := do
  let (header, reader1) ← parseBlockHeaderAfterMagic reader
  let (huffman, reader2) ← parseHuffmanMetadata header reader1
  pure ({ header := header, huffman := huffman }, reader2)

/-- Parse an end-of-stream section after its marker. -/
def parseEndOfStreamAfterMarker (reader : BitReader) : Except String (EndOfStream × BitReader) := do
  let (streamCRC, reader1) ← reader.readBits 32
  pure ({ streamCRC := UInt32.ofNat streamCRC }, reader1)

/-- Parse the next top-level section from an exact `.bz2` stream. -/
def parseSection (reader : BitReader) : Except String (Section × BitReader) := do
  let (marker, reader1) ← parseSectionMarker reader
  match marker with
  | .block =>
      let (metadata, reader2) ← parseBlockSectionAfterMarker reader1
      pure (.block metadata, reader2)
  | .eos =>
      let (trailer, reader2) ← parseEndOfStreamAfterMarker reader1
      pure (.eos trailer, reader2)

end Bzip2.Format.BZ2
