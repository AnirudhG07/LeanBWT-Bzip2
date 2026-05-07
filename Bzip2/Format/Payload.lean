import Bzip2.ByteCodec
import Bzip2.Format.Bytes

/-!
Binary serialization for a bz2-like block payload built from the current proved
byte-specialized compressed payload.

This no longer stores the whole abstract payload as a custom tagged blob.
Instead, it uses fields closer to a real bzip2 block:
- `randomised` (always `0`) plus `origPtr`,
- a used-byte symbol map,
- the MTF/RLE payload entries.
-/

namespace Bzip2.Format

set_option autoImplicit false

private def bitMaskAt (i : Nat) : Nat :=
  2 ^ (15 - i)

private def bitIsSet (mask i : Nat) : Bool :=
  (mask / bitMaskAt i) % 2 = 1

private def countSentinels : List (Symbol Nat) → Nat
  | [] => 0
  | none :: xs => countSentinels xs + 1
  | some _ :: xs => countSentinels xs

private def usedBytesOfAlphabet (alphabet : List (Symbol Nat)) : Except String (List Nat) := do
  if countSentinels alphabet ≠ 1 then
    throw "Block alphabet must contain the sentinel exactly once."
  let usedBytes := alphabet.filterMap id
  if usedBytes.eraseDups.length ≠ usedBytes.length then
    throw "Block alphabet contains duplicate byte symbols."
  if usedBytes.any (fun n => 255 < n) then
    throw "Block alphabet contains a symbol outside byte range."
  pure usedBytes

private def groupMask (group : Nat) (usedBytes : List Nat) : Nat :=
  (List.range 16).foldl
    (fun acc offset =>
      if group * 16 + offset ∈ usedBytes then
        acc + bitMaskAt offset
      else
        acc)
    0

private def groupBitmap (usedBytes : List Nat) : Nat :=
  (List.range 16).foldl
    (fun acc group =>
      if groupMask group usedBytes = 0 then
        acc
      else
        acc + bitMaskAt group)
    0

private def encodeUsedByteMap (alphabet : List (Symbol Nat)) : Except String (List UInt8) := do
  let usedBytes ← usedBytesOfAlphabet alphabet
  let groups := groupBitmap usedBytes
  let groupMasks :=
    (List.range 16).foldl
      (fun acc group =>
        let mask := groupMask group usedBytes
        if mask = 0 then
          acc
        else
          acc ++ u16ToBytes mask)
      []
  pure (u16ToBytes groups ++ groupMasks)

private def bytesFromGroupMask (group mask : Nat) : List Nat :=
  (List.range 16).filterMap (fun offset =>
    if bitIsSet mask offset then
      some (group * 16 + offset)
    else
      none)

private def decodeUsedByteMapAux :
    Nat → Nat → Nat → List UInt8 → Except String (List Nat × List UInt8)
  | 0, _, _, rest => pure ([], rest)
  | fuel + 1, group, groupsBitmap, rest =>
      if bitIsSet groupsBitmap group then do
        let (mask, rest') ← readU16 rest
        let (tail, rest'') ← decodeUsedByteMapAux fuel (group + 1) groupsBitmap rest'
        pure (bytesFromGroupMask group mask ++ tail, rest'')
      else
        decodeUsedByteMapAux fuel (group + 1) groupsBitmap rest

private def decodeUsedByteMap (rest : List UInt8) :
    Except String (List (Symbol Nat) × List UInt8) := do
  let (groupsBitmap, rest') ← readU16 rest
  let (usedBytes, rest'') ← decodeUsedByteMapAux 16 0 groupsBitmap rest'
  pure (none :: usedBytes.map some, rest'')

private def encodePayloadEntries : List (Nat × Nat) → Except String (List UInt8)
  | [] => .ok []
  | (v, n) :: rest => do
      if v > U16Max then
        throw "Payload MTF value exceeds UInt16 limit."
      if n > U32Max then
        throw "Payload run length exceeds UInt32 limit."
      let tail ← encodePayloadEntries rest
      pure (u16ToBytes v ++ u32ToBytes n ++ tail)

private def decodePayloadEntries :
    Nat → List UInt8 → Except String (List (Nat × Nat) × List UInt8)
  | 0, rest => .ok ([], rest)
  | n + 1, rest => do
      let (v, rest1) ← readU16 rest
      let (count, rest2) ← readU32 rest1
      let (tail, rest3) ← decodePayloadEntries n rest2
      pure ((v, count) :: tail, rest3)

/-- Serialize the current abstract byte payload into a bz2-like block payload. -/
def encodePayload (payload : Bzip2.ByteCompressed) : Except String ByteArray := do
  if payload.primary > U24Max then
    throw "Primary index exceeds UInt24 limit."
  if payload.payload.length > U32Max then
    throw "Payload entry count exceeds UInt32 limit."
  let symbolMap ← encodeUsedByteMap payload.alphabet
  let body ← encodePayloadEntries payload.payload
  pure <| byteArrayOfList <|
    [0]
    ++ u24ToBytes payload.primary
    ++ symbolMap
    ++ u32ToBytes payload.payload.length
    ++ body

/-- Deserialize the current abstract byte payload from the bz2-like block payload. -/
def decodePayload (bytes : ByteArray) : Except String Bzip2.ByteCompressed := do
  let raw := bytes.toList
  let (randomised, rest0) ← readByte raw
  if randomised ≠ 0 then
    throw "Randomised blocks are not supported."
  let (primary, rest1) ← readU24 rest0
  let (alphabet, rest2) ← decodeUsedByteMap rest1
  let (payloadCount, rest3) ← readU32 rest2
  let (entries, rest4) ← decodePayloadEntries payloadCount rest3
  if rest4 ≠ [] then
    throw "Trailing bytes remain after decoding block payload."
  pure
    { primary := primary
    , alphabet := alphabet
    , payload := entries
    }

end Bzip2.Format
