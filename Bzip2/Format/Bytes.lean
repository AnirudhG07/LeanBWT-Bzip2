import Mathlib

/-!
Shared byte-level helpers for transitional binary format work.

These helpers are intentionally small and self-contained so they can be reused
by the Huffman adapter, payload serializer, and future `.bz2` framing code.
-/

namespace Bzip2.Format

set_option autoImplicit false

abbrev U16Max : Nat := 65535
abbrev U32Max : Nat := 4294967295

def byteArrayOfList (xs : List UInt8) : ByteArray :=
  ByteArray.mk xs.toArray

def u16ToBytes (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n / 256), UInt8.ofNat n]

def u32ToBytes (n : Nat) : List UInt8 :=
  [ UInt8.ofNat (n / 16777216)
  , UInt8.ofNat (n / 65536)
  , UInt8.ofNat (n / 256)
  , UInt8.ofNat n
  ]

def readByte : List UInt8 → Except String (UInt8 × List UInt8)
  | [] => .error "Unexpected end of input while reading byte."
  | b :: bs => .ok (b, bs)

def takeN : Nat → List UInt8 → Except String (List UInt8 × List UInt8)
  | 0, bs => .ok ([], bs)
  | _ + 1, [] => .error "Unexpected end of input while taking bytes."
  | n + 1, b :: bs => do
      let (xs, rest) ← takeN n bs
      pure (b :: xs, rest)

def readU16 : List UInt8 → Except String (Nat × List UInt8) := fun bs => do
  let (raw, rest) ← takeN 2 bs
  match raw with
  | [b1, b2] => pure (b1.toNat * 256 + b2.toNat, rest)
  | _ => .error "Invalid input while reading UInt16."

def readU32 : List UInt8 → Except String (Nat × List UInt8) := fun bs => do
  let (raw, rest) ← takeN 4 bs
  match raw with
  | [b1, b2, b3, b4] =>
      pure
        ( b1.toNat * 16777216
        + b2.toNat * 65536
        + b3.toNat * 256
        + b4.toNat
        , rest
        )
  | _ => .error "Invalid input while reading UInt32."

end Bzip2.Format
