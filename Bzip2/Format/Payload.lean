import Bzip2.ByteCodec
import Bzip2.Format.Bytes

/-!
Binary serialization for the current abstract byte-specialized compressed
payload. This is still a transitional container, but it is binary-safe and no
longer routes data through UTF-8 text encoding.
-/

namespace Bzip2.Format

set_option autoImplicit false

private def payloadMagic : List UInt8 :=
  [0x4c, 0x42, 0x50, 0x31] -- "LBP1"

private def encodeSymbolByte (s : Symbol Nat) : Except String (List UInt8)
  := match s with
  | none => .ok [0]
  | some n =>
      if n < 256 then
        .ok [1, UInt8.ofNat n]
      else
        .error "Payload alphabet contains a symbol outside byte range."

private def decodeSymbolByte : List UInt8 → Except String (Symbol Nat × List UInt8)
  | [] => .error "Unexpected end of input while decoding alphabet symbol."
  | 0 :: rest => .ok (none, rest)
  | 1 :: b :: rest => .ok (some b.toNat, rest)
  | _ :: _ => .error "Invalid alphabet symbol tag."

private def encodeAlphabet : List (Symbol Nat) → Except String (List UInt8)
  | [] => .ok []
  | s :: ss => do
      let head ← encodeSymbolByte s
      let tail ← encodeAlphabet ss
      pure (head ++ tail)

private def decodeAlphabet :
    Nat → List UInt8 → Except String (List (Symbol Nat) × List UInt8)
  | 0, rest => .ok ([], rest)
  | n + 1, rest => do
      let (head, rest') ← decodeSymbolByte rest
      let (tail, rest'') ← decodeAlphabet n rest'
      pure (head :: tail, rest'')

private def encodePayloadEntries : List (Nat × Nat) → Except String (List UInt8)
  | [] => .ok []
  | (v, n) :: rest => do
      if v > U32Max then
        throw "Payload value exceeds UInt32 limit."
      if n > U32Max then
        throw "Payload run length exceeds UInt32 limit."
      let tail ← encodePayloadEntries rest
      pure (u32ToBytes v ++ u32ToBytes n ++ tail)

private def decodePayloadEntries :
    Nat → List UInt8 → Except String (List (Nat × Nat) × List UInt8)
  | 0, rest => .ok ([], rest)
  | n + 1, rest => do
      let (v, rest1) ← readU32 rest
      let (count, rest2) ← readU32 rest1
      let (tail, rest3) ← decodePayloadEntries n rest2
      pure ((v, count) :: tail, rest3)

/-- Serialize the current abstract byte payload into a binary-safe representation. -/
def encodePayload (payload : Bzip2.ByteCompressed) : Except String ByteArray := do
  if payload.primary > U32Max then
    throw "Primary index exceeds UInt32 limit."
  if payload.alphabet.length > U16Max then
    throw "Alphabet size exceeds UInt16 limit."
  if payload.payload.length > U32Max then
    throw "Payload entry count exceeds UInt32 limit."
  let alphaBytes ← encodeAlphabet payload.alphabet
  let body ← encodePayloadEntries payload.payload
  pure <| byteArrayOfList <|
    payloadMagic
    ++ u32ToBytes payload.primary
    ++ u16ToBytes payload.alphabet.length
    ++ alphaBytes
    ++ u32ToBytes payload.payload.length
    ++ body

/-- Deserialize the current abstract byte payload from its binary-safe representation. -/
def decodePayload (bytes : ByteArray) : Except String Bzip2.ByteCompressed := do
  let raw := bytes.toList
  let (magic, rest0) ← takeN 4 raw
  if magic ≠ payloadMagic then
    throw "Invalid payload magic header."
  let (primary, rest1) ← readU32 rest0
  let (alphaCount, rest2) ← readU16 rest1
  let (alphabet, rest3) ← decodeAlphabet alphaCount rest2
  let (payloadCount, rest4) ← readU32 rest3
  let (entries, rest5) ← decodePayloadEntries payloadCount rest4
  if rest5 ≠ [] then
    throw "Trailing bytes remain after decoding payload."
  pure
    { primary := primary
    , alphabet := alphabet
    , payload := entries
    }

end Bzip2.Format
