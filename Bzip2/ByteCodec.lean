import Bzip2.Correctness

/-!
Native byte-oriented bridge from the semantic spec to executable `ByteArray`
values.

This file sits on the boundary between:
- `Bzip2.Spec`, which defines the abstract semantics, and
- `Bzip2.Native`, which exposes operational byte-level APIs.

The definitions here are intentionally format-agnostic: they do not define an
on-disk container and instead just transport the proved abstract payload to and
from `ByteArray`.
-/

namespace Bzip2

set_option autoImplicit false

/-- Current proved compressed payload specialized to bytes. -/
abbrev ByteCompressed := Compressed Nat

/-- View a `ByteArray` as a list of bytes for the proved spec layer. -/
def byteArrayToList (data : ByteArray) : List Nat :=
  data.data.toList.map UInt8.toNat

/-- Convert a list of bytes back into a `ByteArray`. -/
def listToByteArray (xs : List Nat) : ByteArray :=
  ByteArray.mk (xs.map UInt8.ofNat).toArray

@[simp]
theorem listToByteArray_byteArrayToList (data : ByteArray) :
    listToByteArray (byteArrayToList data) = data := by
  cases data with
  | mk arr =>
      simp [byteArrayToList, listToByteArray, List.map_map]
      rw [← Array.toArray_toList (xs := arr)]
      simp
      apply congrArg List.toArray
      nth_rewrite 2 [← List.map_id arr.toList]
      apply List.map_congr_left
      intro b hb
      exact UInt8.toNat.inj (by simp)

/-- Compress raw bytes using the proved abstract BWT pipeline. -/
def compressBytes (data : ByteArray) : ByteCompressed :=
  compress (byteArrayToList data)

/-- Decompress a byte-specialized abstract payload back into raw bytes. -/
def decompressBytes (c : ByteCompressed) : ByteArray :=
  listToByteArray (decompress c)

/-- Byte-oriented roundtrip inherited directly from the abstract correctness theorem. -/
theorem decompressBytes_compressBytes_eq (data : ByteArray) :
    decompressBytes (compressBytes data) = data := by
  have hspec :
      decompress (compress (byteArrayToList data)) = byteArrayToList data := by
    simpa using (decompress_compress_eq (α := Nat) (xs := byteArrayToList data))
  calc
    decompressBytes (compressBytes data)
        = listToByteArray (decompress (compress (byteArrayToList data))) := by
            rfl
    _ = listToByteArray (byteArrayToList data) := by rw [hspec]
    _ = data := listToByteArray_byteArrayToList data

end Bzip2
