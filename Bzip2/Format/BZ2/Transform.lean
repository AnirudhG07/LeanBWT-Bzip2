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

private def appendByteArray (left right : ByteArray) : ByteArray :=
  right.foldl ByteArray.push left

private def spanRunAux (byte : UInt8) : Nat → List UInt8 → Nat × List UInt8
  | count, [] => (count, [])
  | count, next :: rest =>
      if next = byte then
        spanRunAux byte (count + 1) rest
      else
        (count, next :: rest)

private def spanRun (byte : UInt8) (rest : List UInt8) : Nat × List UInt8 :=
  spanRunAux byte 1 rest

private def replicateByte (count : Nat) (byte : UInt8) : ByteArray :=
  Bzip2.Format.byteArrayOfList (List.replicate count byte)

private def runTokens (byte : UInt8) : Nat → List (ByteArray × ByteArray)
  | 0 => []
  | 1 => [(replicateByte 1 byte, replicateByte 1 byte)]
  | 2 => [(replicateByte 1 byte, replicateByte 1 byte), (replicateByte 1 byte, replicateByte 1 byte)]
  | 3 =>
      [ (replicateByte 1 byte, replicateByte 1 byte)
      , (replicateByte 1 byte, replicateByte 1 byte)
      , (replicateByte 1 byte, replicateByte 1 byte)
      ]
  | count =>
      let chunkLen := min count 255
      let head :=
        ( replicateByte chunkLen byte
        , Bzip2.Format.byteArrayOfList [byte, byte, byte, byte, UInt8.ofNat (chunkLen - 4)]
        )
      if count = chunkLen then
        [head]
      else
        head :: runTokens byte (count - chunkLen)

private def tokenizeRunsWithFuel : Nat → List UInt8 → List (ByteArray × ByteArray)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, byte :: rest =>
      let (count, tail) := spanRun byte rest
      runTokens byte count ++ tokenizeRunsWithFuel fuel tail

private def tokenizeRuns (bytes : List UInt8) : List (ByteArray × ByteArray) :=
  tokenizeRunsWithFuel bytes.length bytes

/-- Encode one block with the initial bzip2 RLE1 transform. -/
def encodeInitialRLE (input : ByteArray) : ByteArray :=
  let tokens := tokenizeRuns input.toList
  tokens.foldl (fun out token => appendByteArray out token.2) ByteArray.empty

/-- Split input bytes into exact `.bz2` blocks without breaking RLE1 tokens. -/
def prepareBlocks (blockSize : Nat) (input : ByteArray) : Except String (List PreparedBlock) := do
  if blockSize = 0 then
    throw "Exact `.bz2` block size must be positive."
  let tokens := tokenizeRuns input.toList
  let blocks :=
    Id.run do
      let mut blocks : List PreparedBlock := []
      let mut currentOriginal := ByteArray.empty
      let mut currentRle1 := ByteArray.empty
      for token in tokens do
        let originalTok := token.1
        let rleTok := token.2
        if currentRle1.size > 0 && blockSize < currentRle1.size + rleTok.size then
          blocks := { original := currentOriginal, rle1 := currentRle1 } :: blocks
          currentOriginal := ByteArray.empty
          currentRle1 := ByteArray.empty
        currentOriginal := appendByteArray currentOriginal originalTok
        currentRle1 := appendByteArray currentRle1 rleTok
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
