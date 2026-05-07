import Mathlib
import Bzip2.BWT

/-!
This file develops structural facts about the Burrows-Wheeler matrix and its
columns. It proves that the sorted matrix is a permutation of the rotations,
identifies the first column with the list of matrix heads, and packages the
tag and uniqueness facts used later in the LF and inverse proofs.
-/

set_option linter.unusedSectionVars false

namespace Bzip2

section MatrixLemmas

variable {α : Type} [DecidableEq α] [LinearOrder α]

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

section LFCorrectness

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

/-- Distinct rotation indices produce distinct rows in `rotations xs`. -/
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
    grind [withSentinel_getElem_eq_bot_iff, Nat.mod_eq_of_lt, List.getElem?_rotate, rotateLeft_eq_rotate,
      rotateLeft]
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

/-- The sorted BWT matrix contains exactly the rotations of `withSentinel xs`. -/
theorem bwtmatrix_perm_rotations (xs : List α) :
    ∀ row : List (Symbol α), row ∈ bwtmatrix xs ↔ row ∈ rotations xs := by
  intro row
  exact bwtmatrix_mem_iff_rotations_mem xs row

/-- The last symbol of a rotation is the cyclic predecessor symbol in `withSentinel xs`. -/
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

/-- A tagged entry in the last column determines a unique in-bounds index. -/
theorem tag_uniqueness_L (L : List (Symbol α)) :
    ∀ i j, i < L.length → j < L.length → tagL L i = tagL L j → i = j := by
  intro i j hi hj hEq
  have hiIdx : L.idxOfNth L[i] (L.countBefore L[i] i) = i := by
    grind
  grind [occBefore_eq_countBefore]

/-- The same uniqueness statement holds for tagged entries in the first column. -/
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

/-- Every tagged last-column entry appears at a unique matching place in the first column. -/
theorem tags_match_between_columns (L : List (Symbol α)) :
    ∀ i, i < L.length → ∃ j, j < (firstColumn L).length ∧ tagF L j = tagL L i := by
  intro i hi
  refine ⟨LF L i, LF_lt_firstColumn_length (L := L) i hi, ?_⟩
  grind [LF_lt_firstColumn_length, tagF_LF_eq_tagL]

/-- `LF` is a bijection on valid row indices of the BWT columns. -/
theorem LF_bijective_on_indices (L : List (Symbol α)) :
    (∀ i, i < L.length → LF L i < L.length) ∧
    (∀ i j, i < L.length → j < L.length → LF L i = LF L j → i = j) := by
  grind [tagF_LF_eq_tagL, tag_uniqueness_L, LF_lt_length (L := L)]

/-- `LF` sends a last-column index to the matching tagged entry in the first column. -/
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

lemma last_getD_shiftRowIdx (xs : List α) (k : Nat) :
    let n := xs.length + 1
    (transform xs).last.getD (shiftRowIdx xs (k % n)) ⊥ =
      (withSentinel xs).getD ((k % n + n - 1) % n) ⊥ := by
  let n := xs.length + 1
  let k' := k % n
  let ys := withSentinel xs
  have hi : shiftRowIdx xs k' < (bwtmatrix xs).length := bwtmatrix_get_shiftRowIdx xs k
  have hget : (bwtmatrix xs).getD (shiftRowIdx xs k') [] = rotateLeft ys k' := by
    simp_all [shiftRowIdx, bwtmatrix, rotations, ys, k', n]
    grind
  have hmap :
      (lastColumn (bwtmatrix xs)).getD (shiftRowIdx xs k') ⊥ =
        ((bwtmatrix xs).getD (shiftRowIdx xs k') []).getLastD ⊥ := by
    simpa [lastColumn] using
      (List.getD_map
        (f := fun row => row.getLastD (⊥ : Symbol α))
        (l := bwtmatrix xs)
        (n := shiftRowIdx xs k')
        (d := []))
  have hgetOpt : ((bwtmatrix xs)[shiftRowIdx xs k']?).getD [] = rotateLeft ys k' := by
    simpa [List.getD_eq_getElem?_getD] using hget
  have hlast :
      ((bwtmatrix xs).getD (shiftRowIdx xs k') []).getLastD ⊥ = (rotateLeft ys k').getLastD ⊥ := by
    simpa using congrArg (fun row => row.getLastD (⊥ : Symbol α)) hget
  calc
    (transform xs).last.getD (shiftRowIdx xs k') ⊥
        = ((bwtmatrix xs).getD (shiftRowIdx xs k') []).getLastD ⊥ := by
            simpa [transform] using hmap
    _ = (rotateLeft ys k').getLastD ⊥ := hlast
    _ = ys.getD ((k' + ys.length - 1) % ys.length) ⊥ := by
          simpa [ys] using (last_symbol_of_shift (xs := xs) k')
    _ = ys.getD ((k' + n - 1) % n) ⊥ := by simp [ys, n, withSentinel_length]
    _ = ys.getD ((k % n + n - 1) % n) ⊥ := by simp [k']

lemma lexLE_eq_true_iff_le (l₁ l₂ : List (Symbol α)) :
    lexLE l₁ l₂ = true ↔ l₁ ≤ l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil =>
          simp [lexLE]
      | cons b l₂ =>
          constructor
          · intro _
            exact le_of_lt (by simp)
          · intro _
            simp [lexLE]
  | cons a l₁ ih =>
      cases l₂ with
      | nil =>
          simp [lexLE]
      | cons b l₂ =>
          by_cases hab : a < b
          · constructor
            · intro _
              exact le_of_lt (by simp [List.cons_lt_cons_iff, hab])
            · intro _
              simp [lexLE, hab]
          · by_cases hba : b < a
            · constructor
              · intro htrue
                simp [lexLE, hab, hba] at htrue
              · intro hle
                exfalso
                rcases (le_iff_lt_or_eq).1 hle with hlt | heq
                · rcases (List.cons_lt_cons_iff).1 hlt with hab' | ⟨habEq, _⟩
                  · exact hab hab'
                  · exact lt_irrefl _ (habEq ▸ hba)
                · injection heq with habEq
                  exact lt_irrefl _ (habEq ▸ hba)
            · have habEq : a = b := le_antisymm (le_of_not_gt hba) (le_of_not_gt hab)
              subst habEq
              simpa [lexLE, hab, hba, le_iff_lt_or_eq, List.cons_lt_cons_iff] using ih l₂

lemma lexLE_trans (l₁ l₂ l₃ : List (Symbol α)) :
    lexLE l₁ l₂ = true → lexLE l₂ l₃ = true → lexLE l₁ l₃ = true := by
  intro h12 h23
  have h12' : l₁ ≤ l₂ := (lexLE_eq_true_iff_le _ _).1 h12
  have h23' : l₂ ≤ l₃ := (lexLE_eq_true_iff_le _ _).1 h23
  exact (lexLE_eq_true_iff_le _ _).2 (le_trans h12' h23')

lemma lexLE_total (l₁ l₂ : List (Symbol α)) :
    lexLE l₁ l₂ = true ∨ lexLE l₂ l₁ = true := by
  by_cases h : l₁ ≤ l₂
  · exact Or.inl ((lexLE_eq_true_iff_le _ _).2 h)
  · exact Or.inr ((lexLE_eq_true_iff_le _ _).2 (le_of_not_ge h))

lemma head_getD_le_of_le (r s : List (Symbol α)) :
    r ≤ s → r.getD 0 ⊥ ≤ s.getD 0 ⊥ := by
  intro h
  cases r with
  | nil =>
      simp
  | cons a rs =>
      cases s with
      | nil =>
          have : False := by
            rcases (le_iff_lt_or_eq).1 h with hlt | heq
            · simp at hlt
            · cases heq
          exact this.elim
      | cons b ss =>
          have hab : a ≤ b := by
            rcases (le_iff_lt_or_eq).1 h with hlt | heq
            · exact List.head_le_of_lt hlt
            · cases heq
              exact le_rfl
          simp_all

lemma first_symbol_of_shift (xs : List α) (i : Nat) :
    let ys := withSentinel xs
    (rotateLeft ys i).getD 0 ⊥ = ys.getD (i % ys.length) ⊥ := by
  let ys := withSentinel xs
  have hlen : 0 < ys.length := by
    simp [ys, withSentinel]
  grind only [rotateLeft_eq_rotate, = List.getD_eq_getElem?_getD,
    List.getElem?_rotate (l := ys) (n := i) (m := 0) hlen]

lemma rotations_heads_eq_withSentinel (xs : List α) :
    (rotations xs).map (fun row => row.getD 0 ⊥) = withSentinel xs := by
  let ys := withSentinel xs
  apply List.ext_getElem
  · simp [rotations]
  · intro i hi₁ hi₂
    have hi : i < ys.length := by
      simpa [rotations, ys] using hi₁
    calc
      ((rotations xs).map (fun row => row.getD 0 ⊥))[i]
          = (rotateLeft ys i).getD 0 ⊥ := by
              simp [rotations, ys]
      _ = ys.getD (i % ys.length) ⊥ := by
            simpa [ys] using (first_symbol_of_shift (xs := xs) i)
      _ = ys.getD i ⊥ := by
            simp [Nat.mod_eq_of_lt hi]
      _ = ys[i] := by
            simpa using (List.getD_eq_getElem (l := ys) (d := (⊥ : Symbol α)) (hn := hi))

lemma rotations_lastColumn_eq_rotate (xs : List α) :
    lastColumn (rotations xs) = (withSentinel xs).rotate xs.length := by
  let ys := withSentinel xs
  apply List.ext_getElem
  · simp [lastColumn, rotations]
  · intro i hi₁ hi₂
    grind [withSentinel_length, lastColumn, rotations, List.getElem_rotate, last_symbol_of_shift]

lemma rotations_lastColumn_perm_withSentinel (xs : List α) :
    List.Perm (lastColumn (rotations xs)) (withSentinel xs) := by
  rw [rotations_lastColumn_eq_rotate]
  exact List.rotate_perm (withSentinel xs) xs.length

lemma matrixHeads_sorted (xs : List α) :
    ((bwtmatrix xs).map (fun row => row.getD 0 ⊥)).SortedLE := by
  let r : List (Symbol α) → List (Symbol α) → Prop := fun row₁ row₂ => lexLE row₁ row₂ = true
  let _ : Std.Total r := ⟨fun a b => by
    rcases lexLE_total a b with hab | hba
    · exact Or.inl hab
    · exact Or.inr hba⟩
  let _ : IsTrans (List (Symbol α)) r := ⟨fun a b c hab hbc => lexLE_trans _ _ _ hab hbc⟩
  have hpairRows : (bwtmatrix xs).Pairwise r := by
    simpa [bwtmatrix, sortRows, r] using
      (List.pairwise_mergeSort' (r := r) (l := rotations xs))
  have hpairHeads : ((bwtmatrix xs).map (fun row => row.getD 0 ⊥)).Pairwise (· ≤ ·) := by
    refine hpairRows.map (fun row => row.getD 0 ⊥) ?_
    intro row₁ row₂ hrows
    exact head_getD_le_of_le _ _ ((lexLE_eq_true_iff_le _ _).1 hrows)
  exact hpairHeads.sortedLE

lemma matrixHeads_perm_withSentinel (xs : List α) :
    List.Perm ((bwtmatrix xs).map (fun row => row.getD 0 ⊥)) (withSentinel xs) := by
  rw [← rotations_heads_eq_withSentinel]
  simpa [bwtmatrix, sortRows] using
    (List.Perm.map
      (f := fun row : List (Symbol α) => row.getD 0 (⊥ : Symbol α))
      (List.mergeSort_perm (rotations xs) lexLE))

lemma transform_last_perm_withSentinel (xs : List α) :
    List.Perm (transform xs).last (withSentinel xs) := by
  have hperm :
      List.Perm (lastColumn (bwtmatrix xs)) (lastColumn (rotations xs)) := by
    simpa [lastColumn, bwtmatrix, sortRows] using
      (List.Perm.map
        (f := fun row : List (Symbol α) => row.getLastD (⊥ : Symbol α))
        (List.mergeSort_perm (rotations xs) lexLE))
  grind [transform, lastColumn, rotations_lastColumn_perm_withSentinel]

/-- Sorting the last column produces the same list as taking heads of the sorted rows. -/
lemma firstColumn_eq_matrixHeads (xs : List α) :
    firstColumn (transform xs).last =
      (bwtmatrix xs).map (fun row => row.getD 0 ⊥) := by
  have hperm :
      List.Perm (firstColumn (transform xs).last)
        ((bwtmatrix xs).map (fun row => row.getD 0 ⊥)) := by
    exact (firstColumn_perm _).trans <|
      (transform_last_perm_withSentinel xs).trans <|
        (matrixHeads_perm_withSentinel xs).symm
  have hsortedFirst : (firstColumn (transform xs).last).SortedLE := by
    simpa [firstColumn] using (List.sortedLE_mergeSort (l := (transform xs).last))
  grind [matrixHeads_sorted, List.Perm.eq_of_sortedLE]

/-- Looking up the sorted first column at `shiftRowIdx xs k` returns the first symbol of that row. -/
lemma first_getD_shiftRowIdx (xs : List α) (k : Nat) :
    let n := xs.length + 1
    (firstColumn (transform xs).last).getD (shiftRowIdx xs (k % n)) ⊥ =
      (withSentinel xs).getD (k % n) ⊥ := by
  let n := xs.length + 1
  let k' := k % n
  let ys := withSentinel xs
  have hk_lt : k' < ys.length := by
    have hk' : k' < n := by
      dsimp [k', n]
      exact Nat.mod_lt k (Nat.zero_lt_succ xs.length)
    grind [withSentinel_length]
  grind [rotateLeft_eq_rotate, List.getElem?_rotate, List.getD, Nat.mod_eq_of_lt hk_lt, firstColumn_eq_matrixHeads,shiftRowIdx, bwtmatrix, rotations, bwtmatrix_get_shiftRowIdx]

/--
Symbol matching for predecessor rows: the first-column symbol at the
predecessor row equals the last-column symbol at the current row.
-/
lemma first_symbol_eq_last_symbol (xs : List α) (k : Nat) :
    let n := xs.length + 1
    let k' := k % n
    let L := (transform xs).last
    (firstColumn L).getD (shiftRowIdx xs ((k' + n - 1) % n)) ⊥ = L.getD (shiftRowIdx xs k') ⊥ := by
  grind [first_getD_shiftRowIdx, last_getD_shiftRowIdx]

end LFCorrectness

end Bzip2
