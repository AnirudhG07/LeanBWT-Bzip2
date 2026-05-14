import Bzip2.Format.Bytes
import Bzip2.Format.BZ2.FastBWT
import Mathlib

/-!
Exact `.bz2` block transform pipeline before entropy coding.

This module contains the block-local transformations used by the exact writer:
- initial RLE1 tokenization and block preparation,
- both the original rotation-based reference BWT and the practical fast BWT,
- used-byte alphabet extraction,
- MTF plus RUNA/RUNB encoding with end-of-block symbol.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

/-- Original bytes paired with their RLE1-encoded pre-BWT block. -/
structure PreparedBlock where
  original : ByteArray
  rle1 : ByteArray
deriving DecidableEq

/-- Standard BWT result for one exact `.bz2` block. -/
structure BWTBlock where
  lastColumn : ByteArray
  origPtr : Nat
deriving DecidableEq

/-- Block data prepared for the exact `.bz2` entropy coder. -/
structure EntropyInput where
  original : ByteArray
  rle1 : ByteArray
  lastColumn : ByteArray
  origPtr : Nat
  usedBytes : List UInt8
  symbols : List Nat
deriving DecidableEq

private def appendRepeatedByte (out : ByteArray) (byte : UInt8) (count : Nat) : ByteArray :=
  Id.run do
    let mut out := out
    for _ in [0:count] do
      out := out.push byte
    pure out

private def appendRle1Chunk (out : ByteArray) (byte : UInt8) (chunkLen : Nat) : ByteArray :=
  if chunkLen ≤ 3 then
    appendRepeatedByte out byte chunkLen
  else
    let out := appendRepeatedByte out byte 4
    out.push (UInt8.ofNat (chunkLen - 4))

private def rle1ChunkEncodedSize (chunkLen : Nat) : Nat :=
  if chunkLen ≤ 3 then chunkLen else 5

private def spanRun (input : ByteArray) (start : Nat) : Nat :=
  Id.run do
    let byte := input[start]!
    let mut count := 1
    let mut index := start + 1
    while index < input.size && input[index]! = byte do
      count := count + 1
      index := index + 1
    pure count

/-- Encode one block with the initial bzip2 RLE1 transform. -/
def encodeInitialRLE (input : ByteArray) : ByteArray :=
  Id.run do
    let mut out := ByteArray.empty
    let mut index := 0
    while index < input.size do
      let byte := input[index]!
      let runLen := spanRun input index
      let mut remaining := runLen
      while remaining > 0 do
        let chunkLen := min remaining 255
        out := appendRle1Chunk out byte chunkLen
        remaining := remaining - chunkLen
      index := index + runLen
    pure out

/-- Split input bytes into exact `.bz2` blocks without breaking RLE1 tokens. -/
def prepareBlocks (blockSize : Nat) (input : ByteArray) : Except String (List PreparedBlock) := do
  if blockSize = 0 then
    throw "Exact `.bz2` block size must be positive."
  let blocks := Id.run do
    let mut blocks : List PreparedBlock := []
    let mut currentOriginal := ByteArray.empty
    let mut currentRle1 := ByteArray.empty
    let mut index := 0
    while index < input.size do
      let byte := input[index]!
      let runLen := spanRun input index
      let mut remaining := runLen
      while remaining > 0 do
        let chunkLen := min remaining 255
        let rleChunkSize := rle1ChunkEncodedSize chunkLen
        if currentRle1.size > 0 && blockSize < currentRle1.size + rleChunkSize then
          blocks := { original := currentOriginal, rle1 := currentRle1 } :: blocks
          currentOriginal := ByteArray.empty
          currentRle1 := ByteArray.empty
        currentOriginal := appendRepeatedByte currentOriginal byte chunkLen
        currentRle1 := appendRle1Chunk currentRle1 byte chunkLen
        remaining := remaining - chunkLen
      index := index + runLen
    if currentRle1.size > 0 then
      blocks := { original := currentOriginal, rle1 := currentRle1 } :: blocks
    pure blocks.reverse
  pure blocks

private def rotationLEAux (bytes : ByteArray) (n i j offset : Nat) : Nat → Bool
  | 0 => true
  | fuel + 1 =>
      let bi := bytes[((i + offset) % n)]!
      let bj := bytes[((j + offset) % n)]!
      if bi < bj then
        true
      else if bj < bi then
        false
      else
        rotationLEAux bytes n i j (offset + 1) fuel

private def rotationLE (bytes : ByteArray) (i j : Nat) : Bool :=
  let n := bytes.size
  if n = 0 then
    true
  else
    rotationLEAux bytes n i j 0 n

/-- Reference cyclic-rotation BWT kept for alignment with the original construction. -/
def transformBWTReference (input : ByteArray) : BWTBlock :=
  let n := input.size
  if n = 0 then
    { lastColumn := ByteArray.empty, origPtr := 0 }
  else
    let sorted := (List.range n).mergeSort (rotationLE input)
    let lastColumn :=
      Bzip2.Format.byteArrayOfList <|
        sorted.map (fun start => input[((start + n - 1) % n)]!)
    { lastColumn := lastColumn, origPtr := sorted.findIdx (· = 0) }

/--
Practical exact `.bz2` BWT used by the runtime encoder.

This delegates to the separate fast implementation while leaving
`transformBWTReference` available for regression checks and future refinement
proofs.
-/
def transformBWT (input : ByteArray) : BWTBlock :=
  let fast := transformFastBWT input
  { lastColumn := fast.lastColumn, origPtr := fast.origPtr }

/-- Sorted list of byte values present in a pre-BWT block. -/
def usedBytes (input : ByteArray) : List UInt8 :=
  input.toList.eraseDups.mergeSort (fun a b => decide (a ≤ b))

private def zeroRunCodeRev : Nat → List Nat
  | 0 => []
  | count =>
      let rec loop : Nat → List Nat → List Nat
        | value, acc =>
            let symbol := if value % 2 = 0 then 0 else 1
            let acc := symbol :: acc
            if value < 2 then
              acc
            else
              loop ((value - 2) / 2) acc
      loop (count - 1) []

private def encodeMtfAux :
    List UInt8 → ByteArray → Nat → Nat → List Nat → List Nat
  | alphabet, bytes, index, zeroCount, accRev =>
      if h : index < bytes.size then
        let byte := bytes[index]
        let mtfIndex := alphabet.findIdx (· = byte)
        let alphabet' := byte :: alphabet.erase byte
        if mtfIndex = 0 then
          encodeMtfAux alphabet' bytes (index + 1) (zeroCount + 1) accRev
        else
          let accRev := zeroRunCodeRev zeroCount ++ accRev
          encodeMtfAux alphabet' bytes (index + 1) 0 ((mtfIndex + 1) :: accRev)
      else
        zeroRunCodeRev zeroCount ++ accRev

/-- Encode the BWT last column with exact `.bz2` MTF plus RUNA/RUNB. -/
def encodeMtfRunaRunb (alphabet : List UInt8) (lastColumn : ByteArray) : List Nat :=
  let accRev := encodeMtfAux alphabet lastColumn 0 0 []
  let endOfBlock := alphabet.length + 1
  (endOfBlock :: accRev).reverse

/-- Prepare one block for exact `.bz2` Huffman coding. -/
def prepareEntropyInput (block : PreparedBlock) : EntropyInput :=
  let bwt := transformBWT block.rle1
  let alphabet := usedBytes block.rle1
  { original := block.original
  , rle1 := block.rle1
  , lastColumn := bwt.lastColumn
  , origPtr := bwt.origPtr
  , usedBytes := alphabet
  , symbols := encodeMtfRunaRunb alphabet bwt.lastColumn
  }

end Bzip2.Format.BZ2
