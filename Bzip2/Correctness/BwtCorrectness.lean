import Mathlib
import Bzip2.BWT

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

lemma last_getD_shiftRowIdx (xs : List α) (k : Nat) :
    let n := xs.length + 1
    (transform xs).last.getD (shiftRowIdx xs (k % n)) ⊥ = (withSentinel xs).getD ((k % n + n - 1) % n) ⊥ := by
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
  calc
    (rotateLeft ys i).getD 0 ⊥ = ((ys.rotate i)[0]?).getD ⊥ := by
      simp [ys, rotateLeft_eq_rotate, List.getD_eq_getElem?_getD]
    _ = ((ys[(0 + i) % ys.length]?).getD ⊥) := by
      rw [List.getElem?_rotate (l := ys) (n := i) (m := 0) hlen]
    _ = ys.getD ((0 + i) % ys.length) ⊥ := by
      simp [List.getD]
    _ = ys.getD (i % ys.length) ⊥ := by
      simp

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
    have hi : i < ys.length := by
      simpa [lastColumn, rotations, ys] using hi₁
    have hmod : ((i + ys.length - 1) % ys.length) < ys.length := by
      exact Nat.mod_lt _ (by simp [ys, withSentinel])
    calc
      (lastColumn (rotations xs))[i]
          = (rotateLeft ys i).getLastD ⊥ := by
              simp [lastColumn, rotations, ys]
      _ = ys.getD ((i + ys.length - 1) % ys.length) ⊥ := by
            simpa [ys] using (last_symbol_of_shift (xs := xs) i)
      _ = ys[((i + ys.length - 1) % ys.length)] := by
            simpa using (List.getD_eq_getElem (l := ys) (d := (⊥ : Symbol α)) (hn := hmod))
      _ = (ys.rotate xs.length)[i] := by
            rw [List.getElem_rotate ys xs.length i hi₂]
            simp [ys, withSentinel_length]

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
  exact by
    simpa [transform] using hperm.trans (rotations_lastColumn_perm_withSentinel xs)

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
  have hsortedHeads : ((bwtmatrix xs).map (fun row => row.getD 0 ⊥)).SortedLE :=
    matrixHeads_sorted xs
  exact hperm.eq_of_sortedLE hsortedFirst hsortedHeads


lemma first_getD_shiftRowIdx (xs : List α) (k : Nat) :
    let n := xs.length + 1
    (firstColumn (transform xs).last).getD (shiftRowIdx xs (k % n)) ⊥ = (withSentinel xs).getD (k % n) ⊥ := by
  let n := xs.length + 1
  let k' := k % n
  let ys := withSentinel xs
  have hi : shiftRowIdx xs k' < (bwtmatrix xs).length := bwtmatrix_get_shiftRowIdx xs k
  have hget : (bwtmatrix xs).getD (shiftRowIdx xs k') [] = rotateLeft ys k' := by
    simp_all [shiftRowIdx, bwtmatrix, rotations, ys, k', n]
    grind
  have hhead0 : ((bwtmatrix xs).getD (shiftRowIdx xs k') []).getD 0 ⊥ = (rotateLeft ys k').getD 0 ⊥ := by
    simpa using congrArg (fun row => row.getD 0 ⊥) hget
  have hk_lt : k' < ys.length := by
    have hk' : k' < n := by
      dsimp [k', n]
      exact Nat.mod_lt k (Nat.zero_lt_succ xs.length)
    simpa [ys, n, withSentinel_length] using hk'
  have hrot0 : (rotateLeft ys k').getD 0 ⊥ = ys.getD k' ⊥ := by
    have h0 : (0 : Nat) < ys.length := by grind
    calc
      (rotateLeft ys k').getD 0 ⊥
          = ((ys.rotate k')[0]?).getD ⊥ := by
              simp [rotateLeft_eq_rotate, List.getD_eq_getElem?_getD]
      _ = ((ys[(0 + k') % ys.length]?).getD ⊥) := by
            rw [List.getElem?_rotate (l := ys) (n := k') (m := 0) h0]
      _ = ys.getD ((0 + k') % ys.length) ⊥ := by
            simp [List.getD]
      _ = ys.getD k' ⊥ := by
            simp [Nat.mod_eq_of_lt hk_lt]
  have hfirst :
      (firstColumn (transform xs).last).getD (shiftRowIdx xs k') ⊥ =
        ((bwtmatrix xs).getD (shiftRowIdx xs k') []).getD 0 ⊥ := by
    calc
      (firstColumn (transform xs).last).getD (shiftRowIdx xs k') ⊥
          = (((bwtmatrix xs).map (fun row => row.getD 0 ⊥)).getD (shiftRowIdx xs k') ⊥) := by
              simpa using
                congrArg
                  (fun l : List (Symbol α) => l.getD (shiftRowIdx xs k') ⊥)
                  (firstColumn_eq_matrixHeads (xs := xs))
      _ = ((bwtmatrix xs).getD (shiftRowIdx xs k') []).getD 0 ⊥ := by
            simpa using
              (List.getD_map
                (f := fun row : List (Symbol α) => row.getD 0 (⊥ : Symbol α))
                (l := bwtmatrix xs)
                (n := shiftRowIdx xs k')
                (d := []))
  grind only


/--
  Symbol matching: (firstColumn L)[j] = head(Rows[j]).
-/
lemma first_symbol_eq_last_symbol (xs : List α) (k : Nat) :
    let n := xs.length + 1
    let k' := k % n
    let L := (transform xs).last
    (firstColumn L).getD (shiftRowIdx xs ((k' + n - 1) % n)) ⊥ = L.getD (shiftRowIdx xs k') ⊥ := by
  let n := xs.length + 1
  let k' := k % n
  let bwt := transform xs
  let L := bwt.last
  let ys := withSentinel xs

  -- 1. L[i] = T[(k'+n-1)%n]
  have hLi : L.getD (shiftRowIdx xs k') ⊥ = ys.getD ((k' + n - 1) % n) ⊥ := by
    grind [last_getD_shiftRowIdx]

  -- 2. F[j] = T[(k'+n-1)%n]
  let j := shiftRowIdx xs ((k' + n - 1) % n)
  have hFj : (firstColumn L).getD j ⊥ = ys.getD ((k' + n - 1) % n) ⊥ := by
    grind [first_getD_shiftRowIdx]
  grind

/--
  Rank matching:
  Since mergeSort is stable and lexicographical comparison c::S1 < c::S2 <-> S1 < S2,
  the rank of 'c' in the last column maps perfectly to the rank of 'c' in the first column.
-/
theorem rank_matching (xs : List α) (k : Nat) :
    let n := xs.length + 1
    let k' := k % n
    let L := (transform xs).last
    let i := shiftRowIdx xs k'
    let j := shiftRowIdx xs ((k' + n - 1) % n)
    rankF L j = rankL L i := by
  let n := xs.length + 1
  let k' := k % n
  let L := (transform xs).last
  let i := shiftRowIdx xs k'
  let j := shiftRowIdx xs ((k' + n - 1) % n)
  let c := L.getD i ⊥

  sorry

theorem tagF_shiftRowIdx_prev_eq_tagL_shiftRowIdx (xs : List α) (k : Nat) :
    let n := xs.length + 1
    let k' := k % n
    let L := (transform xs).last
    tagF L (shiftRowIdx xs ((k' + n - 1) % n)) = tagL L (shiftRowIdx xs k') := by
  apply Prod.ext
  · exact first_symbol_eq_last_symbol xs k
  · exact rank_matching xs k

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

  have hkprev_lt : ((k' + n - 1) % n) < n := by
    refine Nat.mod_lt ((k' + n - 1)) ?_
    exact Nat.zero_lt_succ xs.length
  have hLi : L.getD i ⊥ = (withSentinel xs).getD ((k' + n - 1) % n) ⊥ := by
    simpa [i, k', n, L, bwt] using (last_getD_shiftRowIdx (xs := xs) k)
  have hFj : (firstColumn L).getD j ⊥ = (withSentinel xs).getD ((k' + n - 1) % n) ⊥ := by
    simpa [j, k', n, L, bwt, Nat.mod_eq_of_lt hkprev_lt] using
      (first_getD_shiftRowIdx (xs := xs) ((k' + n - 1) % n))
  have htag : tagF L j = tagL L i := by
    simpa [i, j, k', n, L, bwt] using
      (tagF_shiftRowIdx_prev_eq_tagL_shiftRowIdx (xs := xs) k)

  apply tag_uniqueness_F L (LF L i) j
  · exact LF_lt_firstColumn_length L i hi
  · exact hj
  · simpa [LF] using (tagF_LF_eq_tagL (L := L) i hi).trans htag.symm

def lfCollectIdx (n k c i : Nat) : Nat :=
  (k + i + (n - 1) * (c + 1)) % n

lemma lfCollectIdx_step (k' n c i : Nat)
    (hn : 0 < n) (hk : k' < n) :
    lfCollectIdx n ((k' + n - 1) % n) c i = lfCollectIdx n k' (Nat.succ c) i := by
  unfold lfCollectIdx
  cases n with
  | zero =>
      cases hn
  | succ m =>
      simp only [Nat.succ_sub_one]
      cases k' with
      | zero =>
          have hsimpl : (0 + (m + 1) - 1 : Nat) = m := by
            omega
          have hmod : m % (m + 1) = m := by
            exact Nat.mod_eq_of_lt (Nat.lt_succ_self m)
          rw [hsimpl, hmod]
          have hmul : m * (c + 2) = m * (c + 1) + m := by
            rw [show c + 2 = (c + 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
          have hs : m + i + m * (c + 1) = i + m * (c + 2) := by
            rw [hmul]
            omega
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            congrArg (fun t => t % (m + 1)) hs
      | succ k =>
          have hk' : k < m + 1 := Nat.lt_of_succ_lt hk
          have hsimpl : (Nat.succ k + (m + 1) - 1 : Nat) = Nat.succ k + m := by
            omega
          have hmod : (Nat.succ k + m) % (m + 1) = k := by
            have hsum : Nat.succ k + m = k + (m + 1) := by
              omega
            calc
              (Nat.succ k + m) % (m + 1) = (k + (m + 1)) % (m + 1) := by
                rw [hsum]
              _ = k % (m + 1) := by rw [Nat.add_mod_right]
              _ = k := Nat.mod_eq_of_lt hk'
          rw [hsimpl, hmod]
          have hmul : m * (c + 2) = m * (c + 1) + m := by
            rw [show c + 2 = (c + 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
          calc
            (k + i + m * (c + 1)) % (m + 1)
                = (k + i + m * (c + 1) + (m + 1)) % (m + 1) := by
                    rw [Nat.add_mod_right]
            _ = (Nat.succ k + i + m * (c + 2)) % (m + 1) := by grind

lemma lfCollectIdx_last (k' n c : Nat)
    (hn : 0 < n) (hk : k' < n) :
    (((k' + n - 1) % n + n - 1) % n) = lfCollectIdx n k' (Nat.succ c) c := by
  unfold lfCollectIdx
  cases n with
  | zero =>
      cases hn
  | succ m =>
      simp only [Nat.succ_sub_one]
      cases k' with
      | zero =>
          have hsimpl : (0 + (m + 1) - 1 : Nat) = m := by
            grind
          have hmod : m % (m + 1) = m := by
            exact Nat.mod_eq_of_lt (Nat.lt_succ_self m)
          rw [hsimpl, hmod]
          calc
            ((m + m) % (m + 1))
                = (((m + m) + (m + 1) * c) % (m + 1)) := by
                    rw [Nat.add_mul_mod_self_left]
            _ = (c + m * (c + 2)) % (m + 1) := by grind
            _ = (0 + c + m * (c.succ + 1)) % (m + 1) := by
                  simp [Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm]
      | succ k =>
          have hk' : k < m + 1 := Nat.lt_of_succ_lt hk
          have hmod : (Nat.succ k + m) % (m + 1) = k := by
            calc
              (Nat.succ k + m) % (m + 1) = (k + (m + 1)) % (m + 1) := by grind
              _ = k % (m + 1) := by rw [Nat.add_mod_right]
              _ = k := Nat.mod_eq_of_lt hk'
          simp_all only [lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, Order.add_one_le_iff,
            Nat.add_succ_sub_one, Nat.succ_eq_add_one]
          calc
            ((k + m) % (m + 1))
                = (((k + m) + (m + 1) * (c + 1)) % (m + 1)) := by
                    rw [Nat.add_mul_mod_self_left]
            _ = (Nat.succ k + c + m * (c + 2)) % (m + 1) := by grind
            _ = (k + 1 + c + m * (c.succ + 1)) % (m + 1) := by grind

/-- Induction lemma: `lfCollect` correctly traverses the string backward. -/
lemma lfCollect_eq_reverse_take (xs : List α) (c : Nat) (k : Nat) :
    let n := xs.length + 1
    let last := (transform xs).last
    let k' := k % n
    (lfCollect last c (shiftRowIdx xs k')).reverse =
      (List.range c).map (fun i => (withSentinel xs).getD (lfCollectIdx n k' c i) ⊥) := by
  induction c generalizing k with
  | zero => simp [lfCollect]
  | succ c ih =>
      let n := xs.length + 1
      let last := (transform xs).last
      let k' := k % n
      let next_k := (k' + n - 1) % n
      have hn : 0 < n := by
        simp [n]
      have hk_lt : k' < n := by
        dsimp [k', n]
        exact Nat.mod_lt k (Nat.zero_lt_succ xs.length)
      have hstep : lfStep last (shiftRowIdx xs k') = shiftRowIdx xs next_k := by
        simpa [LF, lfStep, n, last, k', next_k] using (LF_of_shiftRowIdx (xs := xs) k)
      have hnext_lt : next_k < n := by
        dsimp [next_k]
        exact Nat.mod_lt (k' + n - 1) (Nat.zero_lt_succ xs.length)
      have ih' :
          (lfCollect last c (shiftRowIdx xs next_k)).reverse =
            (List.range c).map (fun i => (withSentinel xs).getD (lfCollectIdx n next_k c i) ⊥) := by
        simpa [n, last, next_k, Nat.mod_eq_of_lt hnext_lt] using (ih next_k)
      have hlast :
          last.getD (shiftRowIdx xs next_k) ⊥ = (withSentinel xs).getD ((next_k + n - 1) % n) ⊥ := by
        simpa [n, last, next_k, Nat.mod_eq_of_lt hnext_lt] using (last_getD_shiftRowIdx (xs := xs) next_k)
      have hlastOpt :
          last[shiftRowIdx xs next_k]?.getD ⊥ = (withSentinel xs).getD ((next_k + n - 1) % n) ⊥ := by
        simpa [List.getD_eq_getElem?_getD] using hlast
      calc
        (lfCollect last (Nat.succ c) (shiftRowIdx xs k')).reverse
            =
              (lfCollect last c (lfStep last (shiftRowIdx xs k'))).reverse ++
                [last.getD (lfStep last (shiftRowIdx xs k')) ⊥] := by
                rw [lfCollect, List.reverse_cons]
        _ = (lfCollect last c (shiftRowIdx xs next_k)).reverse ++ [last.getD (shiftRowIdx xs next_k) ⊥] := by
              rw [hstep]
        _ = (List.range c).map (fun i => (withSentinel xs).getD (lfCollectIdx n next_k c i) ⊥) ++
              [(withSentinel xs).getD ((next_k + n - 1) % n) ⊥] := by
                simp [ih', hlastOpt, List.getD_eq_getElem?_getD]
        _ = (List.range (Nat.succ c)).map
              (fun i => (withSentinel xs).getD (lfCollectIdx n k' (Nat.succ c) i) ⊥) := by
                rw [List.range_succ, List.map_append, List.map_singleton]
                congr 1
                · refine List.map_congr_left (fun i hi => ?_)
                  have hidx := lfCollectIdx_step k' n c i hn hk_lt
                  simpa using congrArg (fun t => (withSentinel xs).getD t ⊥) hidx
                · have hidx := lfCollectIdx_last k' n c hn hk_lt
                  simpa using congrArg (fun t => (withSentinel xs).getD t ⊥) hidx

lemma lfCollectIdx_full (n i : Nat) (hn : 0 < n) :
    lfCollectIdx n 0 n i = ((n - 1 + i) % n) := by
  unfold lfCollectIdx
  cases n with
  | zero =>
      cases hn
  | succ m =>
      simp only [Nat.succ_sub_one]
      have hmul : m * (m + 2) = (m + 1) * m + m := by
        rw [show m + 2 = (m + 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
        rw [Nat.mul_comm m (m + 1)]
      have hsum : i + ((m + 1) * m + m) = (i + m) + (m + 1) * m := by
        omega
      calc
        (0 + i + m * (m + 2)) % (m + 1)
            = (i + ((m + 1) * m + m)) % (m + 1) := by rw [Nat.zero_add, hmul]
        _ = ((i + m) + (m + 1) * m) % (m + 1) := by rw [hsum]
        _ = (i + m) % (m + 1) := by rw [Nat.add_mul_mod_self_left]
        _ = (m + i) % (m + 1) := by rw [Nat.add_comm]

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

lemma stripSentinel_cons_map (xs : List α) :
    stripSentinel (⊥ :: xs.map (fun x => (x : Symbol α))) = xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp_all
      exact
        Eq.symm
          (List.append_cancel_left
            (congrArg (HAppend.hAppend xs) (congrArg (List.cons x) (id (Eq.symm ih)))))

theorem inverse_transform_from_LF (xs : List α) :
    inverse (transform xs) = xs := by
  let n := xs.length + 1
  let ys := withSentinel xs
  let bwt := transform xs
  let last := bwt.last
  let primary := bwt.primary
  have hnpos : 0 < n := by
    simp [n]
  have hyslen : ys.length = n := by
    simp [ys, n, withSentinel_length]
  have hlast : last.length = n := by
    simpa [n, bwt, last, transform, lastColumn] using (bwtmatrix_length (xs := xs))

  have hprim : primary = shiftRowIdx xs 0 := by
    simp [transform, bwt, primary, shiftRowIdx, rotations, rotateLeft, withSentinel]
  have hcollect' :
      (lfCollect last n (shiftRowIdx xs 0)).reverse =
        (List.range n).map (fun i => ys.getD (lfCollectIdx n 0 n i) ⊥) := by
    simpa only [n, ys, last, Nat.mod_eq_of_lt hnpos] using
      (lfCollect_eq_reverse_take (xs := xs) (c := n) (k := 0))
  have hcollectIdx :
      (List.range n).map (fun i => ys.getD (lfCollectIdx n 0 n i) ⊥) =
        (List.range n).map (fun i => ys.getD ((n - 1 + i) % n) ⊥) := by
    refine List.map_congr_left (fun i hi => ?_)
    have hidx := lfCollectIdx_full n i hnpos
    simpa [ys] using congrArg (fun t => ys.getD t ⊥) hidx
  have hrotateMapAux :
      (List.range n).map (fun i => ys.getD ((n - 1 + i) % n) ⊥) =
        (List.range n).map (fun i => (rotateLeft ys (n - 1)).getD i ⊥) := by
    refine List.map_congr_left (fun i hi => ?_)
    have hi : i < n := List.mem_range.mp hi
    have hiys : i < ys.length := by
      simpa [hyslen] using hi
    have hrot :
        (rotateLeft ys (n - 1)).getD i ⊥ = ys.getD ((i + (n - 1)) % ys.length) ⊥ := by
      calc
        (rotateLeft ys (n - 1)).getD i ⊥
            = ((ys.rotate (n - 1))[i]?).getD ⊥ := by
                simp [rotateLeft_eq_rotate, List.getD_eq_getElem?_getD]
        _ = ((ys[(i + (n - 1)) % ys.length]?).getD ⊥) := by
              rw [List.getElem?_rotate (l := ys) (n := n - 1) (m := i) hiys]
        _ = ys.getD ((i + (n - 1)) % ys.length) ⊥ := by
              simp [List.getD]
    simpa [hyslen, Nat.add_comm] using hrot.symm
  have hrotateMap :
      (List.range n).map (fun i => ys.getD ((n - 1 + i) % n) ⊥) = rotateLeft ys (n - 1) := by
    calc
      (List.range n).map (fun i => ys.getD ((n - 1 + i) % n) ⊥)
          = (List.range n).map (fun i => (rotateLeft ys (n - 1)).getD i ⊥) := hrotateMapAux
      _ = rotateLeft ys (n - 1) := by
            simpa [rotateLeft, hyslen] using (map_getD_range (ys := rotateLeft ys (n - 1)))
  have hstriprot : stripSentinel (rotateLeft ys (n - 1)) = xs := by
    have hkrot : n - 1 < ys.length := by
      simp_all [ys, n, withSentinel_length]
    have hrotform : rotateLeft ys (n - 1) = ⊥ :: xs.map (fun x => (x : Symbol α)) := by
      simp [ys, rotateLeft, withSentinel, n]
    rw [hrotform]
    exact stripSentinel_cons_map xs
  calc
    inverse (transform xs)
        = stripSentinel ((lfCollect last last.length primary).reverse) := by
            simp [inverse, inverseAlgorithmic, inverseFromLast, bwt, last, primary]
    _ = stripSentinel ((lfCollect last n primary).reverse) := by grind
    _ = stripSentinel ((lfCollect last n (shiftRowIdx xs 0)).reverse) := by grind
    _ = stripSentinel ((List.range n).map (fun i => ys.getD (lfCollectIdx n 0 n i) ⊥)) := by grind
    _ = stripSentinel ((List.range n).map (fun i => ys.getD ((n - 1 + i) % n) ⊥)) := by grind
    _ = stripSentinel (rotateLeft ys (n - 1)) := by grind
    _ = xs := hstriprot


/-- Main BWT round-trip theorem. -/
theorem inverse_transform (xs : List α) :
    inverse (transform xs) = xs := by
  exact inverse_transform_from_LF xs

/-- End-to-end compression/decompression correctness theorem. -/
theorem decompress_compress (xs : List α) :
    decompress (compress xs) = xs := by
  simp [compress, decompress, rleDecode_rleEncode]
  sorry

end LFCorrectness

end Bzip2
