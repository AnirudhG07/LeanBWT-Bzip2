import Mathlib

/-!
Big-endian bit reader for exact `.bz2` decoding work.

Bits are consumed most-significant-bit first within each byte, matching the
real bzip2 format.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

/-- Reader state over a byte array with a bit-level cursor. -/
structure BitReader where
  bytes : ByteArray
  bitPos : Nat := 0

/-- Start reading from the beginning of a byte array. -/
def BitReader.ofByteArray (bytes : ByteArray) : BitReader :=
  { bytes := bytes }

/-- Total number of bits left to read. -/
def BitReader.bitsRemaining (reader : BitReader) : Nat :=
  reader.bytes.size * 8 - reader.bitPos

/-- Whether the current cursor is byte-aligned. -/
def BitReader.isByteAligned (reader : BitReader) : Bool :=
  reader.bitPos % 8 = 0

/-- Advance the reader to the next byte boundary. -/
def BitReader.alignToByte (reader : BitReader) : BitReader :=
  if reader.isByteAligned then
    reader
  else
    let rem := reader.bitPos % 8
    { reader with bitPos := reader.bitPos + (8 - rem) }

/-- Read one bit from the stream. -/
def BitReader.readBit (reader : BitReader) : Except String (Bool × BitReader) := do
  if h : reader.bitPos < reader.bytes.size * 8 then
    let byteIndex := reader.bitPos / 8
    let bitIndex := reader.bitPos % 8
    have hByte : byteIndex < reader.bytes.size := by
      omega
    let byte := reader.bytes[byteIndex]
    let bit := ((byte.toNat / (2 ^ (7 - bitIndex))) % 2 = 1)
    pure (bit, { reader with bitPos := reader.bitPos + 1 })
  else
    throw "Unexpected end of input while reading bit."

private def readBitsAux : Nat → Nat → BitReader → Except String (Nat × BitReader)
  | 0, acc, reader => pure (acc, reader)
  | n + 1, acc, reader => do
      let (bit, reader') ← reader.readBit
      let acc' := acc * 2 + if bit then 1 else 0
      readBitsAux n acc' reader'

/-- Read exactly `count` bits as a big-endian natural number. -/
def BitReader.readBits (reader : BitReader) (count : Nat) :
    Except String (Nat × BitReader) :=
  readBitsAux count 0 reader

end Bzip2.Format.BZ2
