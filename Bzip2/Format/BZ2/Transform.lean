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

/-! ### RLE1 token model

The initial bzip2 RLE1 transform is defined structurally on a list of
`(byte, chunkLength)` tokens so its round trip and block-splitting properties
are provable. The runtime encoder uses exactly these functions.
-/

/-- Encoded byte width of one RLE1 chunk: literal copies below 4, else 4 + a count byte. -/
def rle1ChunkEncodedSize (chunkLen : Nat) : Nat :=
  if chunkLen ≤ 3 then chunkLen else 5

/-- Wire bytes for one RLE1 chunk of `chunkLen` copies of `byte`. -/
def rle1ChunkBytes (byte : UInt8) (chunkLen : Nat) : List UInt8 :=
  if chunkLen ≤ 3 then
    List.replicate chunkLen byte
  else
    List.replicate 4 byte ++ [UInt8.ofNat (chunkLen - 4)]

/-- Count of leading copies of `byte` at the front of `xs`. -/
def leadingRun (byte : UInt8) : List UInt8 → Nat
  | [] => 0
  | x :: xs => if x = byte then leadingRun byte xs + 1 else 0

theorem leadingRun_le (byte : UInt8) (xs : List UInt8) :
    leadingRun byte xs ≤ xs.length := by
  induction xs with
  | nil => simp [leadingRun]
  | cons x xs ih =>
      simp only [leadingRun, List.length_cons]
      split <;> omega

/-- Split a run of `length` equal bytes into chunks of at most 255. -/
def runChunks (byte : UInt8) : Nat → List (UInt8 × Nat)
  | 0 => []
  | length + 1 =>
      let chunk := min (length + 1) 255
      (byte, chunk) :: runChunks byte (length + 1 - chunk)
termination_by length => length
decreasing_by omega

/-- Push the chunks of one run onto a reversed token accumulator. -/
def pushRunChunksRev (byte : UInt8) : Nat → List (UInt8 × Nat) → List (UInt8 × Nat)
  | 0, acc => acc
  | length + 1, acc =>
      let chunk := min (length + 1) 255
      pushRunChunksRev byte (length + 1 - chunk) ((byte, chunk) :: acc)
termination_by length => length
decreasing_by omega

/--
Tail-recursive worker for `rle1Tokens`: `cur`/`count` is the run in progress,
`acc` is the reversed token list. Structural on the remaining input, so it
compiles to a loop and is stack-safe on full-size blocks.
-/
def rle1TokensRev : UInt8 → Nat → List UInt8 → List (UInt8 × Nat) → List (UInt8 × Nat)
  | cur, count, [], acc => pushRunChunksRev cur count acc
  | cur, count, x :: xs, acc =>
      if x = cur then
        rle1TokensRev cur (count + 1) xs acc
      else
        rle1TokensRev x 1 xs (pushRunChunksRev cur count acc)

/-- Decompose input bytes into the maximal-run RLE1 token stream. -/
def rle1Tokens : List UInt8 → List (UInt8 × Nat)
  | [] => []
  | byte :: xs => (rle1TokensRev byte 1 xs []).reverse

/-- Append the wire bytes for one RLE1 token to `out`. -/
def appendTokenBytes (out : ByteArray) (token : UInt8 × Nat) : ByteArray :=
  (rle1ChunkBytes token.1 token.2).foldl ByteArray.push out

/-- Encode one block with the initial bzip2 RLE1 transform. -/
def encodeInitialRLE (input : ByteArray) : ByteArray :=
  (rle1Tokens input.toList).foldl appendTokenBytes ByteArray.empty

/-- Original bytes contributed by one RLE1 token. -/
private def tokenOriginal (token : UInt8 × Nat) : ByteArray :=
  Bzip2.Format.byteArrayOfList (List.replicate token.2 token.1)

/-- Wire bytes contributed by one RLE1 token. -/
private def tokenRle1 (token : UInt8 × Nat) : ByteArray :=
  Bzip2.Format.byteArrayOfList (rle1ChunkBytes token.1 token.2)

/-- Greedily pack RLE1 tokens into blocks bounded by `blockSize` encoded bytes. -/
def packTokens (blockSize : Nat) :
    List (UInt8 × Nat) → ByteArray → ByteArray → List PreparedBlock
  | [], curOriginal, curRle1 =>
      if curRle1.size > 0 then [{ original := curOriginal, rle1 := curRle1 }] else []
  | token :: rest, curOriginal, curRle1 =>
      let chunkSize := rle1ChunkEncodedSize token.2
      if curRle1.size > 0 && blockSize < curRle1.size + chunkSize then
        { original := curOriginal, rle1 := curRle1 } ::
          packTokens blockSize rest (tokenOriginal token) (tokenRle1 token)
      else
        packTokens blockSize rest
          (curOriginal ++ tokenOriginal token) (curRle1 ++ tokenRle1 token)

/-- Split input bytes into exact `.bz2` blocks without breaking RLE1 tokens. -/
def prepareBlocks (blockSize : Nat) (input : ByteArray) : Except String (List PreparedBlock) := do
  if blockSize = 0 then
    throw "Exact `.bz2` block size must be positive."
  pure (packTokens blockSize (rle1Tokens input.toList) ByteArray.empty ByteArray.empty)

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

/--
Bijective base-2 digits of a zero-run length, least-significant first.
Symbol `0` is RUNA (weight `1`), symbol `1` is RUNB (weight `2`); the digit at
position `i` carries weight `2 ^ i`. This is the structural, provable form of
the RUNA/RUNB encoding of a run of zeros.
-/
def zeroRunDigits : Nat → List Nat
  | 0 => []
  | count + 1 => (count % 2) :: zeroRunDigits (count / 2)
termination_by n => n
decreasing_by omega

/-- The zero-run symbols in stream order (most-significant digit first). -/
def zeroRunCodeRev (count : Nat) : List Nat := (zeroRunDigits count).reverse

def encodeMtfAux :
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
