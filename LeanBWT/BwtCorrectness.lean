import Mathlib
import LeanBWT.BWT

namespace LeanBWT

section RLE
variable {α : Type} [DecidableEq α]

/-- Helper lemma for run-length decoding of one encoded run block. -/
lemma rleDecode_rleAux (current : α) (count : Nat) (xs : List α) :
    rleDecode (rleAux current count xs) = List.replicate count current ++ xs := by
  induction xs generalizing current count with
  | nil =>
      simp [rleAux, rleDecode]
  | cons y ys ih =>
      by_cases h : y = current
      · simp [rleAux, h, ih, List.replicate_add, List.append_assoc]
      · simp [rleAux, h, rleDecode, ih]

/-- RLE round-trip theorem. -/
theorem rleDecode_rleEncode (xs : List α) :
    rleDecode (rleEncode xs) = xs := by
  cases xs with
  | nil =>
      simp [rleEncode, rleDecode]
  | cons x xs =>
      simpa [rleEncode] using (rleDecode_rleAux (α := α) x 1 xs)

end RLE

section BWT
variable {α : Type} [Ord α] [Inhabited α] [DecidableEq α]

/-- Main BWT round-trip theorem. -/
theorem inverse_transform (xs : List α) :
    let (last, primary) := transform xs
    inverse last primary = xs := by
  -- TODO: complete formal proof for the iterative inverse-table algorithm.
  sorry

/-- End-to-end correctness theorem. -/
theorem decompress_compress (xs : List α) :
    decompress (compress xs) = xs := by
  rcases h : transform xs with ⟨last, primary⟩
  have hInv : inverse last primary = xs := by
    simpa [h] using (inverse_transform (α := α) xs)
  simpa [compress, decompress, h, rleDecode_rleEncode] using hInv

end BWT

end LeanBWT
