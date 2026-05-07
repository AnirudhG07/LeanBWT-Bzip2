import Bzip2.Format.Bytes
import Huffman.Codec

/-!
Byte-archive wrapper built on top of the external `LeanHuffmanCoding` codec.

This module delegates Huffman tree construction plus symbol encode/decode to the
dependency, while keeping the surrounding byte container in this repository.
-/

namespace Bzip2.Format.HuffmanArchive

set_option autoImplicit false

abbrev PackedByteStream := ByteArray

private def magicHeader : List UInt8 :=
  [0x4c, 0x48, 0x55, 0x46] -- "LHUF"

private def packBitsAux : BitStream → Nat → Nat → List UInt8 → List UInt8
  | [], current, usedBits, acc =>
      if usedBits = 0 then
        acc.reverse
      else
        let padded := UInt8.ofNat (current * (2 ^ (8 - usedBits)))
        (padded :: acc).reverse
  | bit :: bits, current, usedBits, acc =>
      let bitNat := if bit then 1 else 0
      let current' := current * 2 + bitNat
      let usedBits' := usedBits + 1
      if usedBits' = 8 then
        packBitsAux bits 0 0 (UInt8.ofNat current' :: acc)
      else
        packBitsAux bits current' usedBits' acc

private def packBits (bits : BitStream) : List UInt8 :=
  packBitsAux bits 0 0 []

private def bitsOfByte (b : UInt8) : List Bool :=
  let n := b.toNat
  [ (n / 128) % 2 = 1
  , (n / 64) % 2 = 1
  , (n / 32) % 2 = 1
  , (n / 16) % 2 = 1
  , (n / 8) % 2 = 1
  , (n / 4) % 2 = 1
  , (n / 2) % 2 = 1
  , n % 2 = 1
  ]

private def bitsFromBytes (bytes : List UInt8) : List Bool :=
  bytes.foldr (fun b acc => bitsOfByte b ++ acc) []

private def readTableEntries :
    Nat → List UInt8 → Except String (FrequencyTable UInt8 × List UInt8)
  | 0, bs => .ok ([], bs)
  | n + 1, bs => do
      let (sym, rest1) ← readByte bs
      let (freq, rest2) ← readU32 rest1
      if freq = 0 then
        throw "Archive contains invalid zero-frequency symbol."
      let (tailEntries, rest3) ← readTableEntries n rest2
      pure ((sym, freq) :: tailEntries, rest3)

private def encodeTableEntries : FrequencyTable UInt8 → Except String (List UInt8)
  | [] => .ok []
  | (sym, freq) :: xs => do
      if freq > U32Max then
        throw "Frequency exceeds archive UInt32 limit."
      let rest ← encodeTableEntries xs
      pure (sym :: (u32ToBytes freq ++ rest))

/-- Pack raw bytes using the upstream Huffman codec and a local byte archive wrapper. -/
def packBytes (input : ByteArray) : Except String PackedByteStream := do
  let symbols := input.toList
  if symbols.isEmpty then
    let header := magicHeader ++ u32ToBytes 0 ++ u16ToBytes 0 ++ u32ToBytes 0
    pure (byteArrayOfList header)
  else
    let codec ← Huffman.buildCodecFromSymbols symbols
    let bits ← Huffman.encodeSymbols codec symbols
    if symbols.length > U32Max then
      throw "Input exceeds archive UInt32 length limit."
    if bits.length > U32Max then
      throw "Encoded bitstream exceeds archive UInt32 length limit."
    if codec.table.length > U16Max then
      throw "Frequency table exceeds archive UInt16 count limit."
    let tableBytes ← encodeTableEntries codec.table
    let payload := packBits bits
    pure <| byteArrayOfList <|
      magicHeader
      ++ u32ToBytes symbols.length
      ++ u16ToBytes codec.table.length
      ++ tableBytes
      ++ u32ToBytes bits.length
      ++ payload

/-- Unpack raw bytes from the local archive wrapper using the upstream Huffman codec. -/
def unpackBytes (archive : ByteArray) : Except String ByteArray := do
  let raw := archive.toList
  let (magic, rest0) ← takeN 4 raw
  if magic ≠ magicHeader then
    throw "Invalid archive magic header."
  let (originalLen, rest1) ← readU32 rest0
  let (tableSize, rest2) ← readU16 rest1
  let (table, rest3) ← readTableEntries tableSize rest2
  let (bitLen, payloadBytes) ← readU32 rest3
  let allBits := bitsFromBytes payloadBytes
  if allBits.length < bitLen then
    throw "Archive payload too short for declared bit length."
  let bits := allBits.take bitLen
  if originalLen = 0 then
    if tableSize = 0 ∧ bitLen = 0 then
      pure ByteArray.empty
    else
      throw "Invalid empty archive metadata."
  else
    if tableSize = 0 then
      throw "Non-empty archive has empty frequency table."
    let codec ← Huffman.buildCodec table
    let decoded ← Huffman.decodeBits codec bits
    if decoded.length ≠ originalLen then
      throw "Decoded symbol count does not match archive metadata."
    pure (byteArrayOfList decoded)

end Bzip2.Format.HuffmanArchive
