import Mathlib
import LeanBWT.BWT

set_option linter.unusedSectionVars false

namespace LeanBWT

section MatrixLemmas

variable {α : Type}

lemma withSentinel_length (xs : List α) :
    (withSentinel xs).length = xs.length + 1 := by
  simp [withSentinel]

lemma rotations_length (xs : List α) :
    (rotations xs).length = xs.length + 1 := by
  simp [rotations, withSentinel]

lemma bwtmatrix_length [LinearOrder α] (xs : List α) :
    (bwtmatrix xs).length = xs.length + 1 := by
  simp [bwtmatrix, sortRows, rotations, withSentinel, List.length_mergeSort]

lemma lastColumn_length (rows : List (List (Symbol α))) :
    (lastColumn rows).length = rows.length := by
  simp [lastColumn]

lemma firstColumn_length [LinearOrder α] (last : List (Symbol α)) :
    (firstColumn last).length = last.length := by
  simp [firstColumn, List.length_mergeSort]

end MatrixLemmas

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

section LFProofs

set_option autoImplicit false

variable {α : Type} [LinearOrder α] [DecidableEq α]

/-- Rank of the symbol at index `j` in the last column. -/
@[simp, grind .]
def rankL (L : List (Symbol α)) (j : Nat) : Nat :=
  occBefore L j (L.getD j ⊥)

/-- Rank of the symbol at index `j` in the first column (`firstColumn L`). -/
@[simp, grind .]
def rankF (L : List (Symbol α)) (j : Nat) : Nat :=
  let F := firstColumn L
  occBefore F j (F.getD j ⊥)

/-- Tagged last-column entry: symbol with its rank among prior equal symbols. -/
@[simp, grind .]
def tagL (L : List (Symbol α)) (j : Nat) : Symbol α × Nat :=
  (L.getD j ⊥, rankL L j)

/-- Tagged first-column entry: symbol with its rank among prior equal symbols. -/
@[simp, grind .]
def tagF (L : List (Symbol α)) (j : Nat) : Symbol α × Nat :=
  let F := firstColumn L
  (F.getD j ⊥, rankF L j)

/-- LF map (first-last jump), currently using `lfStep` from `BWT.lean`. -/
@[simp, grind .]
def LF (L : List (Symbol α)) (j : Nat) : Nat :=
  let F := firstColumn L
  let c := L.getD j ⊥
  let k := occBefore L j c
  F.idxOfNth c k

lemma rankL_def (L : List (Symbol α)) (j : Nat) :
    rankL L j = occBefore L j (L.getD j ⊥) := rfl

lemma rankF_def (L : List (Symbol α)) (j : Nat) :
    rankF L j = occBefore (firstColumn L) j ((firstColumn L).getD j ⊥) := by
  simp [rankF]

lemma tagL_fst (L : List (Symbol α)) (j : Nat) :
    (tagL L j).1 = L.getD j ⊥ := by
  simp [tagL]

lemma tagF_fst (L : List (Symbol α)) (j : Nat) :
    (tagF L j).1 = (firstColumn L).getD j ⊥ := by
  simp [tagF]

lemma occBefore_eq_countBefore (xs : List (Symbol α)) (i : Nat) (c : Symbol α) :
    occBefore xs i c = xs.countBefore c i := by
  simp [occBefore, List.countBefore_eq_count_take]

lemma bwtmatrix_mem_iff_rotations_mem (xs : List α) (row : List (Symbol α)) :
    row ∈ bwtmatrix xs ↔ row ∈ rotations xs := by
  simp_all [bwtmatrix, sortRows]

lemma firstColumn_mem_iff (L : List (Symbol α)) (c : Symbol α) :
    c ∈ firstColumn L ↔ c ∈ L := by
  simp_all [firstColumn]

lemma rotateLeft_eq_rotate {β : Type} (xs : List β) (i : Nat) :
    rotateLeft xs i = xs.rotate i := by
  grind [rotateLeft, List.rotate]

lemma bot_not_mem_withSentinel_prefix (xs : List α) :
    (⊥ : Symbol α) ∉ (List.map (fun x => x) (do let a ← xs; pure ((a : Symbol α)))) := by
  simp

lemma withSentinel_getElem_eq_bot_iff (xs : List α) (k : Nat)
    (hk : k < (withSentinel xs).length) :
    (withSentinel xs)[k] = (⊥ : Symbol α) ↔ k = xs.length := by
  let pref : List (Symbol α) := List.map (fun x => x) (do let a ← xs; pure ((a : Symbol α)))
  have hprefLen : pref.length = xs.length := by
    simp [pref]
  grind [bot_not_mem_withSentinel_prefix, withSentinel]

/-
  Theorems below are the full LF-based proof chain.
-/

theorem rotations_nodup (xs : List α) :
    List.Nodup (rotations xs) := by
  let ys := withSentinel xs
  have hlen : ys.length = xs.length + 1 := by
    grind [withSentinel_length]
  unfold rotations
  refine (List.nodup_map_iff_inj_on List.nodup_range).2 ?_
  intro i hi j hj hEq
  let m : Nat := xs.length - i
  have hbot_at_m_i : (rotateLeft ys i)[m]? = some (⊥ : Symbol α) := by
    grind [withSentinel_getElem_eq_bot_iff, Nat.mod_eq_of_lt, List.getElem?_rotate, rotateLeft_eq_rotate, rotateLeft]
  have horig_j_opt : ys[(m + j) % ys.length]? = some (⊥ : Symbol α) := by
    grind [List.getElem?_rotate, rotateLeft, rotateLeft_eq_rotate]
  have hs_mod : (xs.length - i + j) % (xs.length + 1) = xs.length := by
    grind [withSentinel_getElem_eq_bot_iff]
  have hs_eq : xs.length - i + j = xs.length := by
    by_cases hsge : xs.length + 1 ≤ xs.length - i + j
    · have hmodsub :
          (xs.length - i + j) % (xs.length + 1)
            = (xs.length - i + j - (xs.length + 1)) % (xs.length + 1) := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            (Nat.mod_eq_sub_mod hsge)
      have hsub_lt : xs.length - i + j - (xs.length + 1) < xs.length + 1 := by
        grind
      have hsub_mod :
          (xs.length - i + j - (xs.length + 1)) % (xs.length + 1)
            = xs.length - i + j - (xs.length + 1) := Nat.mod_eq_of_lt hsub_lt
      grind
    · have hslt : xs.length - i + j < xs.length + 1 := Nat.lt_of_not_ge hsge
      rw [Nat.mod_eq_of_lt hslt] at hs_mod
      exact hs_mod
  grind [withSentinel, rotateLeft_eq_rotate, List.getElem?_rotate, rotateLeft]

theorem bwtmatrix_perm_rotations (xs : List α) :
    ∀ row : List (Symbol α), row ∈ bwtmatrix xs ↔ row ∈ rotations xs := by
  intro row
  exact bwtmatrix_mem_iff_rotations_mem xs row

theorem last_symbol_of_shift (xs : List α) (i : Nat) :
    ((rotateLeft (withSentinel xs) i).getLastD ⊥) =
      (withSentinel xs).getD ((i + (withSentinel xs).length - 1) % (withSentinel xs).length) ⊥ := by
  let ys := withSentinel xs
  have hlen : 0 < ys.length := by
    simp [ys, withSentinel]
  have hidx : ys.length - 1 < ys.length := by
    exact Nat.sub_lt (Nat.succ_le_of_lt hlen) (Nat.succ_pos _)
  have harg : i + ys.length - 1 = i + (ys.length - 1) :=
    Nat.add_sub_assoc (Nat.succ_le_of_lt hlen) i
  calc
    (rotateLeft ys i).getLastD ⊥
        = (ys.rotate i).getLastD ⊥ := by simp [rotateLeft_eq_rotate]
    _ = (((ys.rotate i)[ys.length - 1]?).getD ⊥) := by
          rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
          simp [List.length_rotate]
    _ = ((ys[((ys.length - 1) + i) % ys.length]?).getD ⊥) := by
          rw [List.getElem?_rotate (l := ys) (n := i) (m := ys.length - 1) hidx]
    _ = ((ys[(i + (ys.length - 1)) % ys.length]?).getD ⊥) := by
          simp [Nat.add_comm]
    _ = ((ys[(i + ys.length - 1) % ys.length]?).getD ⊥) := by
          simp [harg]
    _ = ys.getD ((i + ys.length - 1) % ys.length) ⊥ := by
          simp [List.getD]
    _ = (withSentinel xs).getD ((i + (withSentinel xs).length - 1) % (withSentinel xs).length) ⊥ := by
          simp [ys]

theorem tag_uniqueness_L (L : List (Symbol α)) :
    ∀ i j, i < L.length → j < L.length → tagL L i = tagL L j → i = j := by
  intro i j hi hj hEq
  have hiIdx : L.idxOfNth L[i] (L.countBefore L[i] i) = i := by
    grind
  grind [occBefore_eq_countBefore]

theorem tag_uniqueness_F (L : List (Symbol α)) :
    ∀ i j, i < (firstColumn L).length → j < (firstColumn L).length → tagF L i = tagF L j → i = j := by
  grind [tag_uniqueness_L]

lemma firstColumn_perm (L : List (Symbol α)) :
    List.Perm (firstColumn L) L := by
  simpa [firstColumn] using (List.mergeSort_perm L (fun a b => decide (a ≤ b)))

lemma rankL_lt_count (L : List (Symbol α)) (i : Nat) (hi : i < L.length) :
    rankL L i < L.count L[i] := by
  simp_all [rankL, occBefore_eq_countBefore, List.getD]

lemma LF_lt_firstColumn_length (L : List (Symbol α)) (i : Nat) (hi : i < L.length) :
    LF L i < (firstColumn L).length := by
  grind [occBefore_eq_countBefore, firstColumn_perm]

lemma LF_lt_length (L : List (Symbol α)) (i : Nat) (hi : i < L.length) :
    LF L i < L.length := by
  simpa [firstColumn, List.length_mergeSort] using LF_lt_firstColumn_length (L := L) i hi

lemma tagF_LF_eq_tagL (L : List (Symbol α)) (i : Nat) (hi : i < L.length) :
    tagF L (LF L i) = tagL L i := by
  grind [occBefore_eq_countBefore, List.getD, firstColumn_perm]

theorem tags_match_between_columns (L : List (Symbol α)) :
    ∀ i, i < L.length → ∃ j, j < (firstColumn L).length ∧ tagF L j = tagL L i := by
  intro i hi
  refine ⟨LF L i, LF_lt_firstColumn_length (L := L) i hi, ?_⟩
  grind [LF_lt_firstColumn_length, tagF_LF_eq_tagL]

theorem LF_bijective_on_indices (L : List (Symbol α)) :
    (∀ i, i < L.length → LF L i < L.length) ∧
    (∀ i j, i < L.length → j < L.length → LF L i = LF L j → i = j) := by
  grind [tagF_LF_eq_tagL, tag_uniqueness_L, LF_lt_length (L := L)]

theorem LF_predecessor_semantics (L : List (Symbol α)) :
    ∀ i, i < L.length → tagF L (LF L i) = tagL L i := by
  intro i hi
  exact tagF_LF_eq_tagL (L := L) i hi

/-- The row index in `bwtmatrix xs` corresponding to `rotateLeft (withSentinel xs) k`. -/
def shiftRowIdx (xs : List α) (k : Nat) : Nat :=
  (bwtmatrix xs).findIdx (fun row => decide (row = rotateLeft (withSentinel xs) k))

lemma bwtmatrix_get_shiftRowIdx (xs : List α) (k : Nat) :
    let n := xs.length + 1
    shiftRowIdx xs (k % n) < (bwtmatrix xs).length := by
  let n := xs.length + 1
  let k' := k % n
  let ys := withSentinel xs
  have hn : ys.length = n := withSentinel_length xs
  have hlen_mat : (bwtmatrix xs).length = n := bwtmatrix_length xs
  have hk_lt : k' < n := by
    simp_all [k']
    refine Nat.mod_lt k ?_
    exact Nat.zero_lt_succ xs.length
  grind [shiftRowIdx, bwtmatrix_mem_iff_rotations_mem]

lemma last_of_shiftRowIdx (xs : List α) (k : Nat) :
    let n := xs.length + 1
    shiftRowIdx xs (k % n) < (transform xs).last.length := by
  simpa [transform, lastColumn] using (bwtmatrix_get_shiftRowIdx (xs := xs) k)

theorem LF_of_shiftRowIdx (xs : List α) (k : Nat) :
    let n := xs.length + 1
    let last := (transform xs).last
    let k' := k % n
    LF last (shiftRowIdx xs k') = shiftRowIdx xs ((k' + n - 1) % n) := by
  let n := xs.length + 1
  let k' := k % n
  let bwt := transform xs
  let L := bwt.last
  let i := shiftRowIdx xs k'
  let j := shiftRowIdx xs ((k' + n - 1) % n)
  have hi : i < L.length := by
    simpa [i, k', n, L, bwt] using (last_of_shiftRowIdx (xs := xs) k)
  have hjL : j < L.length := by
    simpa [j, k', n, L, bwt] using (last_of_shiftRowIdx (xs := xs) ((k' + n - 1) % n))
  have hj : j < (firstColumn L).length := by
    simpa [firstColumn, List.length_mergeSort] using hjL
  -- TODO
  have htag : tagF L j = tagL L i := by
    sorry
  apply tag_uniqueness_F L (LF L i) j
  · exact LF_lt_firstColumn_length L i hi
  · exact hj
  · simpa [LF] using (tagF_LF_eq_tagL (L := L) i hi).trans htag.symm

/-- Induction lemma: `lfCollect` correctly traverses the string backward. -/
lemma lfCollect_eq_reverse_take (xs : List α) (c : Nat) (k : Nat) :
    let n := xs.length + 1
    let last := (transform xs).last
    let k' := k % n
    (lfCollect last c (shiftRowIdx xs k')).reverse =
      (List.range c).map (fun i => (withSentinel xs).getD ((k' + n - (c + 1) + i) % n) ⊥) := by
  induction c generalizing k with
  | zero => simp [lfCollect]
  | succ c ih =>
      let n := xs.length + 1
      let last := (transform xs).last
      let k' := k % n
      have hstep : lfStep last (shiftRowIdx xs k') = shiftRowIdx xs ((k' + n - 1) % n) := by
        simpa [LF, lfStep, n, last, k'] using (LF_of_shiftRowIdx (xs := xs) k)
      have ih' := ih ((k' + n - 1) % n)
      simp [n, k'] at ih'
      apply?

      -- TODO
      sorry

lemma map_getD_range (ys : List (Symbol α)) :
    (List.range ys.length).map (fun i => ys.getD i ⊥) = ys := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
      simpa [List.range_succ_eq_map, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using congrArg (List.cons y) ih

lemma stripSentinel_withSentinel (xs : List α) :
    stripSentinel (withSentinel xs) = xs := by
  induction xs with
  | nil =>
      simp_all [stripSentinel, withSentinel]
      intros; expose_names; exact List.mem_singleton.mp h

  | cons x xs ih =>
      simp_all [stripSentinel, withSentinel]
      exact
        Eq.symm
          (List.append_cancel_left
            (congrArg (HAppend.hAppend xs) (congrArg (List.cons x) (id (Eq.symm ih)))))

theorem inverse_transform_from_LF (xs : List α) :
    inverse (transform xs) = xs := by
  let n := xs.length + 1
  let bwt := transform xs
  let last := bwt.last
  let primary := bwt.primary
  have hnpos : 0 < n := by
    simp [n]
  have hlast : last.length = n := by
    simpa [n, bwt, last, transform, lastColumn] using (bwtmatrix_length (xs := xs))

  have hprim : primary = shiftRowIdx xs 0 := by
    simp [transform, bwt, primary, shiftRowIdx, rotations, rotateLeft, withSentinel]
  have hcollect := lfCollect_eq_reverse_take (xs := xs) (c := n) (k := 0)
  simp [n, Nat.mod_eq_of_lt hnpos] at hcollect
  have hcollect' :
      (lfCollect last n (shiftRowIdx xs 0)).reverse =
        (List.range n).map (fun i => (withSentinel xs).getD (i % n) ⊥) := by grind
  have hmod :
      (List.range n).map (fun i => (withSentinel xs).getD (i % n) ⊥) =
        (List.range n).map (fun i => (withSentinel xs).getD i ⊥) := by
    refine List.map_congr_left ?_
    intro i hi
    have hi' : i < n := List.mem_range.mp hi
    simp [Nat.mod_eq_of_lt hi']
  calc
    inverse (transform xs)
        = stripSentinel ((lfCollect last last.length primary).reverse) := by
            simp [inverse, inverseAlgorithmic, inverseFromLast, bwt, last, primary]
    _ = stripSentinel ((lfCollect last n primary).reverse) := by
          simp [hlast]
    _ = stripSentinel ((lfCollect last n (shiftRowIdx xs 0)).reverse) := by simp [hprim]
    _ = stripSentinel ((List.range n).map (fun i => (withSentinel xs).getD (i % n) ⊥)) := by
          simpa using congrArg stripSentinel hcollect'
    _ = stripSentinel ((List.range n).map (fun i => (withSentinel xs).getD i ⊥)) := by
          simpa [stripSentinel] using congrArg stripSentinel hmod
    _ = stripSentinel (withSentinel xs) := by
          simpa [withSentinel_length] using congrArg stripSentinel (map_getD_range (ys := withSentinel xs))
    _ = xs := by simpa using (stripSentinel_withSentinel (xs := xs))

end LFProofs

section BWT

variable {α : Type} [LinearOrder α] [DecidableEq α]

/-- Main BWT round-trip theorem in the clean API shape. -/
theorem inverse_transform (xs : List α) :
    inverse (transform xs) = xs := by
  exact inverse_transform_from_LF xs

/-- End-to-end compression/decompression correctness theorem. -/
theorem decompress_compress (xs : List α) :
    decompress (compress xs) = xs := by
  simp [compress, decompress, rleDecode_rleEncode]
  simpa [transform] using (inverse_transform xs)

end BWT

end LeanBWT
