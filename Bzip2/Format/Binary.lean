import Bzip2.Format.Payload
import Bzip2.Format.CRC32
import Bzip2.Format.HuffmanArchive
import Bzip2.Format.Bytes

/-!
Binary-safe archive API for the current proved abstract compressor.

This is still a transitional format, not final `.bz2`, but it moves the
library onto a byte-oriented container with Huffman-coded outer packing
built on the external `LeanHuffmanCoding` codec.
-/

namespace Bzip2.Format

set_option autoImplicit false

private def archiveMagic : List UInt8 :=
  [0x4c, 0x42, 0x5a, 0x31] -- "LBZ1"

private def archiveVersion : UInt8 :=
  1

/-- Compress raw bytes into the transitional binary archive format. -/
def compressBinary? (data : ByteArray) : Except String ByteArray := do
  let payload := Bzip2.compressBytes data
  let rawPayload ← encodePayload payload
  let packed ← HuffmanArchive.packBytes rawPayload
  if data.size > U32Max then
    throw "Input exceeds archive UInt32 length limit."
  if packed.size > U32Max then
    throw "Packed payload exceeds archive UInt32 length limit."
  let checksum := crc32 data
  pure <| byteArrayOfList <|
    archiveMagic
    ++ [archiveVersion]
    ++ u32ToBytes data.size
    ++ u32ToBytes checksum.toNat
    ++ u32ToBytes packed.size
    ++ packed.toList

/-- Decompress bytes from the transitional binary archive format. -/
def decompressBinary? (archive : ByteArray) : Except String ByteArray := do
  let raw := archive.toList
  let (magic, rest0) ← takeN 4 raw
  if magic ≠ archiveMagic then
    throw "Invalid archive magic header."
  let (version, rest1) ← readByte rest0
  if version ≠ archiveVersion then
    throw "Unsupported archive version."
  let (expectedLen, rest2) ← readU32 rest1
  let (expectedCrc, rest3) ← readU32 rest2
  let (packedLen, rest4) ← readU32 rest3
  let (packedBytes, rest5) ← takeN packedLen rest4
  if rest5 ≠ [] then
    throw "Trailing bytes remain after decoding archive."
  let rawPayload ← HuffmanArchive.unpackBytes (byteArrayOfList packedBytes)
  let payload ← decodePayload rawPayload
  let decoded := Bzip2.decompressBytes payload
  if decoded.size ≠ expectedLen then
    throw "Decoded byte length does not match archive metadata."
  if (crc32 decoded |>.toNat) != expectedCrc then
    throw "Decoded archive checksum does not match archive metadata."
  pure decoded

end Bzip2.Format
