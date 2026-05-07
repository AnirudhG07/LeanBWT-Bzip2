import Bzip2.Format.Payload
import Bzip2.Format.CRC32
import Bzip2.Format.HuffmanArchive
import Bzip2.Format.Bytes

/-!
`.bz2`-inspired block stream wrapper for the current proved abstract
compressor.

This keeps the proved BWT/MTF/RLE core exactly as-is, but wraps it in a
block-oriented stream with a `BZh`-style header, per-block CRCs, and an
end-of-stream marker plus combined CRC. The payload inside each block is still
LeanBzip2-specific, so the result is structurally similar to `.bz2` but not
wire-compatible with `libbzip2`.
-/

namespace Bzip2.Format

set_option autoImplicit false

/-- Low-level stream configuration for the bz2-like archive wrapper. -/
structure StreamConfig where
  /-- Digit written after `BZh`. Real bzip2 uses `1` through `9`. -/
  blockSizeDigit : Nat
  /-- Actual bytes placed into each independently compressed block. -/
  blockBytes : Nat
deriving Inhabited, Repr

/-- Default stream configuration: `BZh1`-style metadata with 100k byte blocks. -/
def defaultStreamConfig : StreamConfig :=
  { blockSizeDigit := 1, blockBytes := 100000 }

/-- Build a real-size bz2-like configuration from the usual `1`-through-`9` digit. -/
def bz2LikeConfig? (blockSizeDigit : Nat) : Except String StreamConfig := do
  if 1 ≤ blockSizeDigit ∧ blockSizeDigit ≤ 9 then
    pure
      { blockSizeDigit := blockSizeDigit
      , blockBytes := blockSizeDigit * 100000
      }
  else
    throw "Block size digit must be between 1 and 9."

private def blockMagic : List UInt8 :=
  [0x31, 0x41, 0x59, 0x26, 0x53, 0x59]

private def endMagic : List UInt8 :=
  [0x17, 0x72, 0x45, 0x38, 0x50, 0x90]

private def streamHeader (config : StreamConfig) : List UInt8 :=
  [0x42, 0x5A, 0x68, UInt8.ofNat (48 + config.blockSizeDigit)]

private def validateConfig (config : StreamConfig) : Except String Unit := do
  if ¬ (1 ≤ config.blockSizeDigit ∧ config.blockSizeDigit ≤ 9) then
    throw "Block size digit must be between 1 and 9."
  if config.blockBytes = 0 then
    throw "Block size in bytes must be positive."
  pure ()

variable {α : Type}

private def chunkListAux : Nat → Nat → List α → List (List α)
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | fuel + 1, chunkSize, xs =>
      let head := xs.take chunkSize
      let tail := xs.drop chunkSize
      head :: chunkListAux fuel chunkSize tail

private def chunkList (chunkSize : Nat) (xs : List α) : List (List α) :=
  chunkListAux (xs.length + 1) chunkSize xs

private def concatByteArrays (blocks : List ByteArray) : ByteArray :=
  byteArrayOfList <| blocks.foldr (fun block acc => block.toList ++ acc) []

private def rotateLeft1 (value : UInt32) : UInt32 :=
  (value <<< 1) ||| (value >>> 31)

private def combineCrc (combined block : UInt32) : UInt32 :=
  rotateLeft1 combined ^^^ block

private def encodeBlockPayload (block : ByteArray) : Except String ByteArray := do
  let payload := Bzip2.compressBytes block
  let rawPayload ← encodePayload payload
  HuffmanArchive.packBytes rawPayload

private def decodeBlockPayload (packed : ByteArray) : Except String ByteArray := do
  let rawPayload ← HuffmanArchive.unpackBytes packed
  let payload ← decodePayload rawPayload
  pure (Bzip2.decompressBytes payload)

private def encodeBlock (block : ByteArray) : Except String (List UInt8) := do
  let packed ← encodeBlockPayload block
  if block.size > U32Max then
    throw "Block exceeds archive UInt32 length limit."
  if packed.size > U32Max then
    throw "Packed block exceeds archive UInt32 length limit."
  let blockCrc := crc32 block
  pure <|
    blockMagic
    ++ u32ToBytes blockCrc.toNat
    ++ u32ToBytes block.size
    ++ u32ToBytes packed.size
    ++ packed.toList

private def parseStreamHeader : List UInt8 → Except String (Nat × List UInt8)
  | 0x42 :: 0x5A :: 0x68 :: digit :: rest =>
      let digitNat := digit.toNat
      if 49 ≤ digitNat ∧ digitNat ≤ 57 then
        pure (digitNat - 48, rest)
      else
        throw "Invalid bz2-like block size digit."
  | _ =>
      throw "Invalid bz2-like archive header."

private def decodeBlocksWithFuel :
    Nat → List UInt8 → UInt32 → List ByteArray →
      Except String (List ByteArray × UInt32 × List UInt8)
  | 0, _, _, _ =>
      throw "Archive decoder did not converge."
  | _ + 1, [], _, _ =>
      throw "Unexpected end of stream while looking for block marker."
  | fuel + 1, raw, combined, acc => do
      let (marker, rest0) ← takeN 6 raw
      if marker = blockMagic then
        let (expectedBlockCrc, rest1) ← readU32 rest0
        let (expectedBlockLen, rest2) ← readU32 rest1
        let (packedLen, rest3) ← readU32 rest2
        let (packedBytes, rest4) ← takeN packedLen rest3
        let decoded ← decodeBlockPayload (byteArrayOfList packedBytes)
        if decoded.size ≠ expectedBlockLen then
          throw "Decoded block length does not match block metadata."
        let actualBlockCrc := crc32 decoded
        if actualBlockCrc.toNat ≠ expectedBlockCrc then
          throw "Decoded block CRC does not match block metadata."
        let combined' := combineCrc combined actualBlockCrc
        decodeBlocksWithFuel fuel rest4 combined' (decoded :: acc)
      else if marker = endMagic then
        let (expectedCombinedCrc, rest1) ← readU32 rest0
        if combined.toNat ≠ expectedCombinedCrc then
          throw "Combined stream CRC does not match end-of-stream metadata."
        pure (acc.reverse, combined, rest1)
      else
        throw "Invalid block or end-of-stream marker."

private def decodeOneStream (raw : List UInt8) : Except String (ByteArray × List UInt8) := do
  let (_digit, rest0) ← parseStreamHeader raw
  let (blocks, _combined, rest1) ← decodeBlocksWithFuel (raw.length + 1) rest0 0 []
  pure (concatByteArrays blocks, rest1)

private def decodeManyStreamsWithFuel :
    Nat → List UInt8 → List ByteArray → Except String ByteArray
  | 0, _, _ =>
      throw "Archive stream decoder did not converge."
  | _ + 1, [], acc =>
      pure <| concatByteArrays acc.reverse
  | fuel + 1, raw, acc => do
      let (decoded, rest) ← decodeOneStream raw
      decodeManyStreamsWithFuel fuel rest (decoded :: acc)

/--
Compress raw bytes using a low-level bz2-like stream configuration.

This is mainly useful for experimentation and testing. For the normal `1`-to-`9`
API, use `bz2LikeConfig?` or the higher-level library wrappers.
-/
def compressBinaryWithConfig? (config : StreamConfig) (data : ByteArray) :
    Except String ByteArray := do
  validateConfig config
  let blockLists := chunkList config.blockBytes data.toList
  let blocks := blockLists.map byteArrayOfList
  let encodedBlocks ← blocks.mapM encodeBlock
  let combined :=
    blocks.foldl (fun acc block => combineCrc acc (crc32 block)) (0 : UInt32)
  pure <| byteArrayOfList <|
    streamHeader config
    ++ encodedBlocks.foldr List.append []
    ++ endMagic
    ++ u32ToBytes combined.toNat

/-- Compress raw bytes into the default bz2-like block archive format. -/
def compressBinary? (data : ByteArray) : Except String ByteArray :=
  compressBinaryWithConfig? defaultStreamConfig data

/-- Decompress bytes from the bz2-like block archive format. -/
def decompressBinary? (archive : ByteArray) : Except String ByteArray :=
  decodeManyStreamsWithFuel (archive.size + 1) archive.toList []

end Bzip2.Format
