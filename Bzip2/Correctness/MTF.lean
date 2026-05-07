import Mathlib
import Bzip2.BWT

/-!
This file proves correctness of the move-to-front stage. The main theorem shows
that `mtfDecode` inverts `mtfEncode` when the alphabet is nodup and contains
every symbol that appears in the message.
-/

set_option linter.unusedSectionVars false

namespace Bzip2

section MTF

variable {β : Type} [DecidableEq β]

/-- `eraseDups` preserves exactly the symbols already present in a list. -/
lemma mem_eraseDups {x : β} :
    ∀ {xs : List β}, x ∈ xs.eraseDups ↔ x ∈ xs
  | [] => by
      simp
  | a :: as => by
      rw [List.eraseDups_cons]
      by_cases hx : x = a
      · repeat grind
      · simp [hx]

/-- `eraseDups` always produces a list with no duplicate entries. -/
lemma nodup_eraseDups :
    ∀ xs : List β, xs.eraseDups.Nodup
  | [] => by
      simp
  | a :: as => by
      rw [List.eraseDups_cons]
      have ih : (List.filter (fun b => !b == a) as).eraseDups.Nodup :=
        nodup_eraseDups _
      simp [List.nodup_cons, ih]
termination_by xs => xs.length
decreasing_by
  simp_wf
  exact List.length_filter_le (fun b => !b == a) as

variable [Inhabited β]

/-- Move-to-front decoding inverts encoding on a nodup alphabet containing all symbols. -/
theorem mtfDecode_mtfEncode_of_nodup
    (alphabet xs : List β)
    (halpha : alphabet.Nodup)
    (hxs : ∀ x ∈ xs, x ∈ alphabet) :
    mtfDecode alphabet (mtfEncode alphabet xs) = xs := by
  induction xs generalizing alphabet with
  | nil =>
      simp [mtfEncode, mtfDecode]
  | cons x xs ih =>
      grind [mtfEncode, mtfDecode]

end MTF

end Bzip2
