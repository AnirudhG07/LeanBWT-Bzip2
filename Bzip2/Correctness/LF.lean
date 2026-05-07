import Bzip2.Correctness.Matrix

/-!
This file proves the core LF facts for the BWT matrix. The main results are
rank matching between the last and first columns, equality of the associated
tags, and the closed formula describing `LF` on rows indexed by
`shiftRowIdx`.
-/

set_option linter.unusedSectionVars false

namespace Bzip2

section LFCorrectness

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {α : Type} [LinearOrder α] [DecidableEq α]

lemma bwtmatrix_perm_rotations' (xs : List α) :
    List.Perm (bwtmatrix xs) (rotations xs) := by
  simpa [bwtmatrix, sortRows] using (List.mergeSort_perm (rotations xs) lexLE)

lemma bwtmatrix_nodup (xs : List α) :
    List.Nodup (bwtmatrix xs) := by
  exact (bwtmatrix_perm_rotations' xs).nodup_iff.2 (rotations_nodup xs)

lemma bwtmatrix_sortedLE (xs : List α) :
    (bwtmatrix xs).SortedLE := by
  let r : List (Symbol α) → List (Symbol α) → Prop := fun row₁ row₂ => lexLE row₁ row₂ = true
  let _ : Std.Total r := ⟨fun a b => by
    rcases lexLE_total a b with hab | hba
    · exact Or.inl hab
    · exact Or.inr hba⟩
  let _ : IsTrans (List (Symbol α)) r := ⟨fun a b c hab hbc => lexLE_trans _ _ _ hab hbc⟩
  have hpairRows : (bwtmatrix xs).Pairwise r := by
    simpa [bwtmatrix, sortRows, r] using
      (List.pairwise_mergeSort' (r := r) (l := rotations xs))
  have hpairLE : (bwtmatrix xs).Pairwise (· ≤ ·) := by
    exact hpairRows.imp (fun {_ _} hrows => (lexLE_eq_true_iff_le _ _).1 hrows)
  exact hpairLE.sortedLE

lemma bwtmatrix_sortedLT (xs : List α) :
    (bwtmatrix xs).SortedLT := by
  exact (bwtmatrix_sortedLE xs).sortedLT_of_nodup (bwtmatrix_nodup xs)

lemma bwtmatrix_row_eq_rotateLeft (xs : List α) (k : Nat) :
    let n := xs.length + 1
    let k' := k % n
    (bwtmatrix xs).getD (shiftRowIdx xs k') [] = rotateLeft (withSentinel xs) k' := by
  let n := xs.length + 1
  let k' := k % n
  let ys := withSentinel xs
  have hi : shiftRowIdx xs k' < (bwtmatrix xs).length := by
    simpa [n, k'] using (bwtmatrix_get_shiftRowIdx (xs := xs) k)
  have hEq : (bwtmatrix xs)[shiftRowIdx xs k'] = rotateLeft ys k' := by
    have htrue :
        decide ((bwtmatrix xs)[shiftRowIdx xs k'] = rotateLeft ys k') = true := by
      simpa [shiftRowIdx, ys] using
        (List.findIdx_getElem
          (xs := bwtmatrix xs)
          (p := fun row => decide (row = rotateLeft ys k'))
          (w := hi))
    simpa using htrue
  simpa [ys] using (List.getD_eq_getElem (l := bwtmatrix xs) (d := []) (hn := hi)).trans hEq

lemma append_singleton_lt_append_singleton_iff {β : Type} [LinearOrder β]
    (s₁ s₂ : List β) (a : β) (hlen : s₁.length = s₂.length) :
    s₁ ++ [a] < s₂ ++ [a] ↔ s₁ < s₂ := by
  induction s₁ generalizing s₂ with
  | nil =>
      cases s₂ with
      | nil =>
          simp
      | cons b s₂ =>
          simp at hlen
  | cons b s₁ ih =>
      cases s₂ with
      | nil =>
          simp at hlen
      | cons c s₂ =>
          have hlen' : s₁.length = s₂.length := by simpa using Nat.succ.inj hlen
          simp [List.cons_lt_cons_iff, ih s₂ hlen']

lemma rotate_last_to_front (l : List (Symbol α)) (h : l ≠ []) :
    l.rotate (l.length - 1) = l.getLastD ⊥ :: l.dropLast := by
  have hlen : 0 < l.length := List.length_pos_of_ne_nil h
  have hlast : l.getLastD (⊥ : Symbol α) = l.getLast h := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast_of_ne_nil h]
    simp
  calc
    l.rotate (l.length - 1)
        = l.drop (l.length - 1) ++ l.take (l.length - 1) := by
            rw [List.rotate_eq_drop_append_take_mod]
            simp [Nat.mod_eq_of_lt (Nat.sub_lt hlen (Nat.succ_pos _))]
    _ = [l.getLast h] ++ l.dropLast := by
          rw [List.drop_length_sub_one h, List.dropLast_eq_take]
    _ = l.getLast h :: l.dropLast := by simp
    _ = l.getLastD ⊥ :: l.dropLast := by rw [hlast]

/-- The predecessor rotation is obtained by moving the last symbol of a row to the front. -/
lemma rotateLeft_predecessor_eq_last_cons_dropLast (xs : List α) (k : Nat) :
    let n := xs.length + 1
    let k' := k % n
    let ys := withSentinel xs
    rotateLeft ys ((k' + n - 1) % n) = (rotateLeft ys k').getLastD ⊥ :: (rotateLeft ys k').dropLast := by
  let n := xs.length + 1
  let k' := k % n
  let ys := withSentinel xs
  let row := rotateLeft ys k'
  have hrow_len : row.length = n := by
    simp [row, ys, n, withSentinel_length, rotateLeft_eq_rotate]
  have hrow_ne : row ≠ [] := by grind only [= List.length_nil]
  calc
    rotateLeft ys ((k' + n - 1) % n)
        = ys.rotate ((k' + n - 1) % n) := by simp [rotateLeft_eq_rotate]
    _ = ys.rotate (k' + n - 1) := by
          simpa [ys, n, withSentinel_length] using (List.rotate_mod ys (k' + n - 1))
    _ = (ys.rotate k').rotate (n - 1) := by grind [List.rotate_rotate]
    _ = row.rotate (n - 1) := by
          grind only [rotateLeft_eq_rotate]
    _ = row.rotate (row.length - 1) := by
          simp [hrow_len]
    _ = row.getLastD ⊥ :: row.dropLast := by
          exact rotate_last_to_front row hrow_ne

/-- Equal-ending rows preserve their order when moved to predecessor form. -/
lemma predecessor_lt_of_same_last {r₁ r₂ : List (Symbol α)}
    (hlen : r₁.length = r₂.length) (h₁ : r₁ ≠ []) (h₂ : r₂ ≠ [])
    (hsame : r₁.getLastD ⊥ = r₂.getLastD ⊥) (hlt : r₁ < r₂) :
    r₁.getLastD ⊥ :: r₁.dropLast < r₂.getLastD ⊥ :: r₂.dropLast := by
  have hsame' : r₁.getLast h₁ = r₂.getLast h₂ := by
    simpa [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h₁, List.getLast?_eq_some_getLast h₂]
      using hsame
  grind only [List.cons_lt_cons_iff, !List.dropLast_concat_getLast,
    append_singleton_lt_append_singleton_iff, = List.length_append]

lemma pred_succ_mod_eq (m n : Nat) (hn : 0 < n) (hm : m < n) :
    ((((m + n - 1) % n) + 1) % n) = m := by
  cases m with
  | zero =>
      have hmod : (n - 1) % n = n - 1 := by
        exact Nat.mod_eq_of_lt (Nat.sub_lt hn (Nat.succ_pos _))
      rw [Nat.zero_add, hmod]
      cases n with
      | zero =>
          cases hn
      | succ k =>
          simp
  | succ m =>
      have hm' : m < n := Nat.lt_of_succ_lt hm
      have hmod : (Nat.succ m + n - 1) % n = m := by
        have hsum : Nat.succ m + n - 1 = m + n := by grind
        calc
          (Nat.succ m + n - 1) % n = (m + n) % n := by rw [hsum]
          _ = m % n := by rw [Nat.add_mod_right]
          _ = m := Nat.mod_eq_of_lt hm'
      rw [hmod]
      simpa using (Nat.mod_eq_of_lt hm)

def rowPred (row : List (Symbol α)) : List (Symbol α) :=
  row.getLastD ⊥ :: row.dropLast

def rowSucc (row : List (Symbol α)) : List (Symbol α) :=
  row.drop 1 ++ [row.getD 0 ⊥]

lemma rowPred_injective_of_ne_nil {r₁ r₂ : List (Symbol α)} (h₁ : r₁ ≠ []) (h₂ : r₂ ≠ []) :
    rowPred r₁ = rowPred r₂ → r₁ = r₂ := by
  grind only [rowPred, !List.dropLast_append_getLast, = List.getLastD_eq_getLast?,
    = List.getLast?_concat, = Option.getD_some]

lemma rowPred_rowSucc_of_ne_nil (row : List (Symbol α)) (h : row ≠ []) :
    rowPred (rowSucc row) = row := by
  cases row with
  | nil =>
      contradiction
  | cons a t =>
      simp [rowPred, rowSucc]

lemma rowSucc_eq_rotateLeft_one (row : List (Symbol α)) (h : row ≠ []) :
    rowSucc row = rotateLeft row 1 := by
  cases row with
  | nil =>
      contradiction
  | cons a t =>
      cases t with
      | nil =>
          simp [rowSucc, rotateLeft]
      | cons b u =>
          have hmod : 1 % (u.length + 2) = 1 := by
            exact Nat.mod_eq_of_lt (by simp)
          simp [rowSucc, rotateLeft, hmod]

lemma mem_bwtmatrix_iff_exists_rotateLeft (xs : List α) (row : List (Symbol α)) :
    row ∈ bwtmatrix xs ↔ ∃ k < xs.length + 1, row = rotateLeft (withSentinel xs) k := by
  rw [bwtmatrix_mem_iff_rotations_mem]
  constructor
  · intro hrow
    rcases List.mem_map.1 hrow with ⟨k, hk, rfl⟩
    exact ⟨k, by simpa [withSentinel_length] using List.mem_range.mp hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    apply List.mem_map.2
    exact ⟨k, by simpa [withSentinel_length] using List.mem_range.mpr hk, rfl⟩

lemma mem_bwtmatrix_length (xs : List α) {row : List (Symbol α)} (hrow : row ∈ bwtmatrix xs) :
    row.length = xs.length + 1 := by
  rcases (mem_bwtmatrix_iff_exists_rotateLeft xs row).1 hrow with ⟨k, hk, rfl⟩
  simp [rotateLeft_eq_rotate, withSentinel_length]

lemma mem_bwtmatrix_ne_nil (xs : List α) {row : List (Symbol α)} (hrow : row ∈ bwtmatrix xs) :
    row ≠ [] := by
  have hlen : row.length = xs.length + 1 := mem_bwtmatrix_length xs hrow
  intro hnil
  simp [hnil] at hlen

/-- `rowPred` on a matrix row agrees with stepping to the previous cyclic shift. -/
lemma rowPred_eq_rotateLeft_pred (xs : List α) (k : Nat) :
    let n := xs.length + 1
    let k' := k % n
    let ys := withSentinel xs
    rowPred (rotateLeft ys k') = rotateLeft ys ((k' + n - 1) % n) := by
  simpa [rowPred] using (rotateLeft_predecessor_eq_last_cons_dropLast (xs := xs) k).symm

/-- Advancing `rowSucc` by one step matches the next cyclic shift. -/
lemma rowSucc_eq_rotateLeft_succ (xs : List α) (k : Nat) :
    let n := xs.length + 1
    let k' := k % n
    let ys := withSentinel xs
    rowSucc (rotateLeft ys k') = rotateLeft ys ((k' + 1) % n) := by
  let n := xs.length + 1
  let k' := k % n
  let ys := withSentinel xs
  have hne : rotateLeft ys k' ≠ [] := by
    have hlen : (rotateLeft ys k').length = n := by
      simp [rotateLeft_eq_rotate, ys, n, withSentinel_length]
    intro hnil
    simp [hnil] at hlen
  calc
    rowSucc (rotateLeft ys k') = rotateLeft (rotateLeft ys k') 1 := by
      exact rowSucc_eq_rotateLeft_one _ hne
    _ = (ys.rotate k').rotate 1 := by
          simp [rotateLeft_eq_rotate]
    _ = ys.rotate (k' + 1) := by
          exact List.rotate_rotate ys k' 1
    _ = ys.rotate ((k' + 1) % n) := by
          simpa [ys, n, withSentinel_length] using (List.rotate_mod ys (k' + 1)).symm
    _ = rotateLeft ys ((k' + 1) % n) := by
          simp [rotateLeft_eq_rotate]

lemma rowPred_mem_of_mem_bwtmatrix (xs : List α) {row : List (Symbol α)}
    (hrow : row ∈ bwtmatrix xs) :
    rowPred row ∈ bwtmatrix xs := by
  rcases (mem_bwtmatrix_iff_exists_rotateLeft xs row).1 hrow with ⟨k, hk, rfl⟩
  let n := xs.length + 1
  let pred := (k + n - 1) % n
  refine (mem_bwtmatrix_iff_exists_rotateLeft xs (rowPred (rotateLeft (withSentinel xs) k))).2 ?_
  refine ⟨pred, Nat.mod_lt _ (Nat.zero_lt_succ xs.length), ?_⟩
  simpa [n, pred, Nat.mod_eq_of_lt hk] using (rowPred_eq_rotateLeft_pred (xs := xs) k)

lemma rowSucc_mem_of_mem_bwtmatrix (xs : List α) {row : List (Symbol α)}
    (hrow : row ∈ bwtmatrix xs) :
    rowSucc row ∈ bwtmatrix xs := by
  rcases (mem_bwtmatrix_iff_exists_rotateLeft xs row).1 hrow with ⟨k, hk, rfl⟩
  let n := xs.length + 1
  let succ := (k + 1) % n
  refine (mem_bwtmatrix_iff_exists_rotateLeft xs (rowSucc (rotateLeft (withSentinel xs) k))).2 ?_
  refine ⟨succ, Nat.mod_lt _ (Nat.zero_lt_succ xs.length), ?_⟩
  simpa [n, succ, Nat.mod_eq_of_lt hk] using (rowSucc_eq_rotateLeft_succ (xs := xs) k)

lemma mem_take_iff_lt_getElem_of_sortedLT {β : Type} [LinearOrder β] {l : List β}
    (hs : l.SortedLT) {i : Nat} (hi : i < l.length) {x : β} (hx : x ∈ l) :
    x ∈ l.take i ↔ x < l[i] := by
  rw [List.mem_take_iff_idxOf_lt hx]
  have hidxlen : l.idxOf x < l.length := (List.idxOf_lt_length_iff).2 hx
  have hxidx : l[l.idxOf x] = x := by
    grind only [= List.getElem_idxOf]
  grind [List.SortedLT.getElem_lt_getElem_iff]

lemma successor_lt_of_same_head {r₁ r₂ : List (Symbol α)}
    (hlen : r₁.length = r₂.length) (h₁ : r₁ ≠ []) (h₂ : r₂ ≠ [])
    (hsame : r₁.getD 0 ⊥ = r₂.getD 0 ⊥) (hlt : r₁ < r₂) :
    rowSucc r₁ < rowSucc r₂ := by
  cases r₁ with
  | nil =>
      contradiction
  | cons a s₁ =>
      cases r₂ with
      | nil =>
          contradiction
      | cons b s₂ =>
          have hab : a = b := by simpa using hsame
          subst hab
          have hlen' : s₁.length = s₂.length := by
            simpa using Nat.succ.inj hlen
          have htail : s₁ < s₂ := by
            simpa [List.cons_lt_cons_iff] using hlt
          have hsucc : s₁ ++ [a] < s₂ ++ [a] := by
            exact (append_singleton_lt_append_singleton_iff _ _ _ hlen').2 htail
          simpa [rowSucc]
            using hsucc

lemma count_map_eq_length_filter_eq {β : Type} [BEq β] [LawfulBEq β] [DecidableEq β]
    (l : List α) (f : α → β) (c : β) :
    List.count c (l.map f) = (l.filter fun x => decide (f x = c)).length := by
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      by_cases h : f x = c
      · simp [h, ih]
      · simp [h, ih]

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
  let rows := bwtmatrix xs
  let ys := withSentinel xs
  let row := rotateLeft ys k'
  let pred := (k' + n - 1) % n
  let prow := rotateLeft ys pred
  let A := (rows.take i).filter (fun r => r.getLastD ⊥ = c)
  let B := (rows.take j).filter (fun r => r.getD 0 ⊥ = c)
  have hi : i < rows.length := by
    simpa [rows, i, n, k'] using (bwtmatrix_get_shiftRowIdx (xs := xs) k)
  have hj : j < rows.length := by
    simpa [rows, j, pred, n] using (bwtmatrix_get_shiftRowIdx (xs := xs) pred)
  have hrowsSorted : rows.SortedLT := by
    simpa [rows] using (bwtmatrix_sortedLT xs)
  have hrowEq : rows[i] = row := by
    grind [bwtmatrix_row_eq_rotateLeft]
  have hprowEq : rows[j] = prow := by
    grind [bwtmatrix_row_eq_rotateLeft]
  have hklt : k' < n := by
    dsimp [k', n]
    exact Nat.mod_lt k (Nat.zero_lt_succ xs.length)
  have hpredlt : pred < n := Nat.mod_lt _ (Nat.zero_lt_succ xs.length)
  have hrowMem : row ∈ rows := by  grind
  have hprowMem : prow ∈ rows := by grind
  have hrowNe : row ≠ [] := mem_bwtmatrix_ne_nil xs hrowMem
  have hprowNe : prow ≠ [] := mem_bwtmatrix_ne_nil xs hprowMem
  have hrowLen : row.length = n := by
    simp [row, ys, n, withSentinel_length, rotateLeft_eq_rotate]
  have hpredRow : rowPred row = prow := by
    simpa [row, prow, pred, ys, n, Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt hpredlt] using
      (rowPred_eq_rotateLeft_pred (xs := xs) k')
  have hsuccProw : rowSucc prow = row := by
    have hsuccIdx : ((pred + 1) % n) = k' := by
      simpa [pred] using pred_succ_mod_eq k' n (by simp [n]) hklt
    grind only [!rowSucc_eq_rotateLeft_succ]
  have hprowHead : prow.getD 0 ⊥ = c := by
    have := congrArg (fun r => r.getD 0 ⊥) hpredRow
    grind only [= List.getD_eq_getElem?_getD, rowPred, = transform.eq_1, = getElem?_pos,
      = List.getElem?_cons, = lastColumn.eq_1, = Option.getD_some, = List.length_map,
      = List.getElem_map]
  have hleftNodup : (A.map rowPred).Nodup := by
    have hTakeNodup : (rows.take i).Nodup := by
      exact (List.take_sublist i rows).nodup hrowsSorted.nodup
    have hAnodup : A.Nodup := by
      exact hTakeNodup.filter _
    refine hAnodup.map_on ?_
    grind only [= List.mem_filter, rowPred_injective_of_ne_nil, → List.mem_of_mem_take,
      mem_bwtmatrix_ne_nil]
  have hrightNodup : B.Nodup := by
    grind only [= List.nodup_iff_count, = List.nodup_iff_pairwise_ne, ← List.Pairwise.filter,
      ← List.Pairwise.take, hrowsSorted.nodup]
  have hmem : ∀ r : List (Symbol α), r ∈ A.map rowPred ↔ r ∈ B := by
    intro r
    constructor
    · intro hr
      rcases List.mem_map.1 hr with ⟨s, hsA, rfl⟩
      grind only [= List.getD_eq_getElem?_getD, = List.mem_filter, mem_bwtmatrix_ne_nil, rowPred,
        → List.mem_of_mem_take, mem_take_iff_lt_getElem_of_sortedLT, = List.getElem?_cons,
        predecessor_lt_of_same_last, rowPred_mem_of_mem_bwtmatrix, = Option.getD_some,
        !mem_bwtmatrix_length]
    · intro hr
      have hrTake : r ∈ rows.take j := List.mem_of_mem_filter hr
      have hrRows : r ∈ rows := List.mem_of_mem_take hrTake
      have hrHead : r.getD 0 ⊥ = c := by grind
      have hrLt : r < prow := by
        grind only [mem_take_iff_lt_getElem_of_sortedLT]
      have hsRows : rowSucc r ∈ rows := by exact rowSucc_mem_of_mem_bwtmatrix xs hrRows
      have hsLt : rowSucc r < row := by
        grind only [successor_lt_of_same_head, mem_bwtmatrix_ne_nil, !mem_bwtmatrix_length]
      grind only [= List.getD_eq_getElem?_getD, = List.mem_map, !rowPred_rowSucc_of_ne_nil,
        mem_bwtmatrix_ne_nil, rowPred, = List.mem_filter, = List.getElem?_cons,
        mem_take_iff_lt_getElem_of_sortedLT, = Option.getD_some]
  have hABlen : (A.map rowPred).length = B.length := by
    have hfinset : (A.map rowPred).toFinset = B.toFinset := by
      ext r
      simp [hmem r]
    rw [← List.toFinset_card_of_nodup hleftNodup, ← List.toFinset_card_of_nodup hrightNodup, hfinset]
  have hrankL : rankL L i = A.length := by
    have hLi : L.getD i ⊥ = c := by
      rfl
    calc
      rankL L i = occBefore (rows.map (fun r => r.getLastD ⊥)) i (L.getD i ⊥) := by
        simp [rankL, L, rows, transform, lastColumn]
      _ = occBefore (rows.map (fun r => r.getLastD ⊥)) i c := by
        rw [hLi]
      _ = A.length := by
        rw [occBefore, ← List.map_take]
        simpa [A] using
          (count_map_eq_length_filter_eq (l := rows.take i) (f := fun r => r.getLastD ⊥) (c := c))
  have hrankF : rankF L j = B.length := by
    have hFL : firstColumn L = rows.map (fun r => r.getD 0 ⊥) := by
      grind only [!firstColumn_eq_matrixHeads]
    have hFj : (firstColumn L).getD j ⊥ = c := by
      calc
        (firstColumn L).getD j ⊥ = ((rows.getD j []).getD 0 ⊥) := by
          rw [hFL]
          simpa using
            (List.getD_map
              (f := fun row : List (Symbol α) => row.getD 0 (⊥ : Symbol α))
              (l := rows) (n := j) (d := []))
        _ = rows[j].getD 0 ⊥ := by
          rw [List.getD_eq_getElem (l := rows) (d := []) (hn := hj)]
        _ = prow.getD 0 ⊥ := by rw [hprowEq]
        _ = c := hprowHead
    calc
      rankF L j = occBefore (rows.map (fun r => r.getD 0 ⊥)) j ((firstColumn L).getD j ⊥) := by
        rw [rankF, hFL]
      _ = occBefore (rows.map (fun r => r.getD 0 ⊥)) j c := by
        rw [hFj]
      _ = B.length := by
        rw [occBefore, ← List.map_take]
        simpa [B] using
          (count_map_eq_length_filter_eq (l := rows.take j) (f := fun r => r.getD 0 ⊥) (c := c))
  grind only [= List.length_map]

/-- The tagged predecessor row in the first column equals the tagged current row in the last column. -/
theorem tagF_shiftRowIdx_prev_eq_tagL_shiftRowIdx (xs : List α) (k : Nat) :
    let n := xs.length + 1
    let k' := k % n
    let L := (transform xs).last
    tagF L (shiftRowIdx xs ((k' + n - 1) % n)) = tagL L (shiftRowIdx xs k') := by
  grind only [!first_symbol_eq_last_symbol, !rank_matching, = tagF.eq_1, = tagL.eq_1]

/-- On rows indexed via `shiftRowIdx`, `LF` moves to the previous cyclic shift. -/
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
    exact last_of_shiftRowIdx xs k
  have hjL : j < L.length := by
    exact last_of_shiftRowIdx xs (k' + n - 1)
  have hkprev_lt : ((k' + n - 1) % n) < n := by
    refine Nat.mod_lt ((k' + n - 1)) ?_
    exact Nat.zero_lt_succ xs.length
  have hLi : L.getD i ⊥ = (withSentinel xs).getD ((k' + n - 1) % n) ⊥ := by
    exact last_getD_shiftRowIdx xs k
  have hFj : (firstColumn L).getD j ⊥ = (withSentinel xs).getD ((k' + n - 1) % n) ⊥ := by
    exact first_getD_shiftRowIdx xs (k' + n - 1)
  have htag : tagF L j = tagL L i := by
    exact tagF_shiftRowIdx_prev_eq_tagL_shiftRowIdx xs k

  apply tag_uniqueness_F L (LF L i) j
  · exact LF_lt_firstColumn_length L i hi
  · grind [firstColumn, List.length_mergeSort]
  · simpa [LF] using (tagF_LF_eq_tagL (L := L) i hi).trans htag.symm

end LFCorrectness

end Bzip2
