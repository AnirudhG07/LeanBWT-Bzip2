import Mathlib

/-!
Exact `.bz2` CRC support.

The wire format uses the forward CRC32 polynomial with the same update rule as
libbzip2 and other compatible decoders.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

private def crcPolynomial : UInt32 :=
  0x04C11DB7

private def crcTableEntry (seed : Nat) : UInt32 :=
  let rec loop : Nat → UInt32 → UInt32
    | 0, crc => crc
    | n + 1, crc =>
        let next :=
          if (crc &&& (0x80000000 : UInt32)) = 0 then
            crc <<< 1
          else
            (crc <<< 1) ^^^ crcPolynomial
        loop n next
  loop 8 (UInt32.ofNat seed <<< 24)

private def crcTable : Array UInt32 :=
  Array.ofFn (fun i : Fin 256 => crcTableEntry i.1)

private def crcStep (crc : UInt32) (byte : UInt8) : UInt32 :=
  let idx := (((crc >>> 24) ^^^ UInt32.ofNat byte.toNat) &&& (0xFF : UInt32)).toNat
  crcTable[idx]! ^^^ (crc <<< 8)

/-- Compute the exact CRC used by `.bz2` blocks and streams. -/
def crc32 (bytes : ByteArray) : UInt32 :=
  let start : UInt32 := 0xFFFFFFFF
  let internal := bytes.foldl crcStep start
  internal ^^^ 0xFFFFFFFF

/-- Fold one block CRC into the rolling `.bz2` stream CRC. -/
def combineStreamCRC (streamCRC blockCRC : UInt32) : UInt32 :=
  ((streamCRC <<< 1) ||| (streamCRC >>> 31)) ^^^ blockCRC

end Bzip2.Format.BZ2
