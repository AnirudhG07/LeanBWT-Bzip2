import Bzip2.Format.Bytes
import Mathlib

/-!
Big-endian bit writer for exact `.bz2` encoding.

Bits are emitted most-significant-bit first within each byte, matching the real
`.bz2` wire format and the companion `BitReader`.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

/-- Writer state for a big-endian bitstream. -/
structure BitWriter where
  bytesRev : List UInt8 := []
  currentByte : Nat := 0
  usedBits : Nat := 0

/-- Empty bit writer. -/
def BitWriter.empty : BitWriter := {}

/-- Whether the current output position is byte-aligned. -/
def BitWriter.isByteAligned (writer : BitWriter) : Bool :=
  writer.usedBits = 0

/-- Emit one bit. -/
def BitWriter.writeBit (writer : BitWriter) (bit : Bool) : BitWriter :=
  let currentByte' := writer.currentByte * 2 + if bit then 1 else 0
  let usedBits' := writer.usedBits + 1
  if usedBits' = 8 then
    { bytesRev := UInt8.ofNat currentByte' :: writer.bytesRev
    , currentByte := 0
    , usedBits := 0
    }
  else
    { writer with currentByte := currentByte', usedBits := usedBits' }

private def writeBitsAux : Nat → Nat → BitWriter → BitWriter
  | 0, _, writer => writer
  | remaining + 1, value, writer =>
      let bit := ((value / (2 ^ remaining)) % 2 = 1)
      writeBitsAux remaining value (writer.writeBit bit)

/-- Emit `count` bits from `value`, most-significant bit first. -/
def BitWriter.writeBits (writer : BitWriter) (count value : Nat) : BitWriter :=
  writeBitsAux count value writer

/-- Emit `count` copies of the same bit. -/
def BitWriter.writeRepeatedBit : BitWriter → Nat → Bool → BitWriter
  | writer, 0, _ => writer
  | writer, count + 1, bit =>
      BitWriter.writeRepeatedBit (writer.writeBit bit) count bit

/-- Pad the output with zero bits until the next byte boundary. -/
def BitWriter.alignToByte (writer : BitWriter) : BitWriter :=
  if writer.isByteAligned then
    writer
  else
    writer.writeRepeatedBit (8 - writer.usedBits) false

/-- Finalize the bitstream, padding the last byte with zeros if needed. -/
def BitWriter.toByteArray (writer : BitWriter) : ByteArray :=
  let writer := writer.alignToByte
  Bzip2.Format.byteArrayOfList writer.bytesRev.reverse

end Bzip2.Format.BZ2
