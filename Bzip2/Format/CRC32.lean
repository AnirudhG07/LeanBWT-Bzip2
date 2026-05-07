/-!
CRC32 checksum support for the transitional binary archive format.

This is a small pure Lean implementation used to detect corruption in the
top-level byte archive wrapper.
-/

namespace Bzip2.Format

set_option autoImplicit false

private def crc32Polynomial : UInt32 :=
  0xEDB88320

private def crc32ByteStep (crc : UInt32) (byte : UInt8) : UInt32 :=
  let start := crc ^^^ UInt32.ofNat byte.toNat
  let rec loop : Nat → UInt32 → UInt32
    | 0, acc => acc
    | n + 1, acc =>
        let shifted := acc >>> 1
        let next :=
          if (acc &&& (1 : UInt32)) = 0 then
            shifted
          else
            shifted ^^^ crc32Polynomial
        loop n next
  loop 8 start

/-- Compute the CRC32 checksum of a byte array. -/
def crc32 (bytes : ByteArray) : UInt32 :=
  let init : UInt32 := 0xFFFFFFFF
  let final := bytes.foldl crc32ByteStep init
  final ^^^ 0xFFFFFFFF

end Bzip2.Format
