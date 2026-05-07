import Mathlib
import Bzip2.BWT

/-!
This file proves correctness of the run-length encoding stage used in the
compression pipeline: decoding the output of `rleEncode` recovers the original
list.
-/

set_option linter.unusedSectionVars false

namespace Bzip2

section RLE

variable {β : Type} [DecidableEq β]

/-- Helper lemma for run-length decoding of one encoded run block. -/
lemma rleDecode_rleAux (current : β) (count : Nat) (xs : List β) :
    rleDecode (rleAux current count xs) = List.replicate count current ++ xs := by
  induction xs generalizing current count with
  | nil =>
      simp [rleAux, rleDecode]
  | cons y ys ih =>
      by_cases h : y = current
      · simp [rleAux, h, ih, List.replicate_add, List.append_assoc]
      · simp [rleAux, h, rleDecode, ih]

/-- RLE round-trip theorem. -/
theorem rleDecode_rleEncode (xs : List β) :
    rleDecode (rleEncode xs) = xs := by
  cases xs with
  | nil =>
      simp [rleEncode, rleDecode]
  | cons x xs =>
      simpa [rleEncode] using (rleDecode_rleAux (β := β) x 1 xs)

end RLE

end Bzip2
