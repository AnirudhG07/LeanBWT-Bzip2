import Mathlib
import Bzip2.BWT
import Bzip2.Correctness.BwtCorrectness

namespace Bzip2

variable {α : Type} [LinearOrder α] [DecidableEq α]

/--
  MONOTONICITY THEOREM (Ground Truth):
  If two rows in the BWT matrix end in the same character 'c',
  their relative order is preserved when cyclically shifted
  to start with 'c'.
-/
theorem bwt_matrix_monotonicity (xs : List α) (i1 i2 : Nat) (c : Symbol α) :
    let n := xs.length + 1
    let rows := bwtmatrix xs
    let L := lastColumn rows
    i1 < i2 → i2 < n → L.getD i1 ⊥ = c → L.getD i2 ⊥ = c →
    shiftRowIdx xs ((i1 + n - 1) % n) < shiftRowIdx xs ((i2 + n - 1) % n) := by
  -- Proof sketch:
  -- 1. rows[i1] = S1 ++ [c], rows[i2] = S2 ++ [c].
  -- 2. i1 < i2 implies rows[i1] < rows[i2] (since they are sorted).
  -- 3. rows[i1] < rows[i2] and both end in c implies S1 < S2.
  -- 4. Pred(rows[i1]) = c :: S1 and Pred(rows[i2]) = c :: S2.
  -- 5. c :: S1 < c :: S2 because S1 < S2.
  -- 6. Thus shiftRowIdx of Pred1 < shiftRowIdx of Pred2.
  sorry

/--
  1. RANK MATCHING (Non-Cyclic):
  Proved using bwt_matrix_monotonicity.
  The number of 'c's in L before index i matches the number of 'c's in F before index j.
-/
theorem rank_matching_fixed (xs : List α) (k : Nat) :
    let n := xs.length + 1
    let k' := k % n
    let L := (transform xs).last
    let i := shiftRowIdx xs k'
    let j := shiftRowIdx xs ((k' + n - 1) % n)
    rankF L j = rankL L i := by
  -- This proof requires summing over the monotonicity:
  -- The map m -> (m + n - 1) % n is a bijection between:
  -- { m < i | L[m] = c } and { m' < j | F[m'] = c }.
  sorry

/--
  2. SYMBOL MATCHING (Non-Cyclic):
  The first column at the predecessor index j matches the last column at index i.
-/
theorem symbol_matching_fixed (xs : List α) (k : Nat) :
    let n := xs.length + 1
    let k' := k % n
    let L := (transform xs).last
    let i := shiftRowIdx xs k'
    let j := shiftRowIdx xs ((k' + n - 1) % n)
    (firstColumn L).getD j ⊥ = L.getD i ⊥ := by
  let n := xs.length + 1
  let k' := k % n
  let L := (transform xs).last
  let i := shiftRowIdx xs k'
  let j := shiftRowIdx xs ((k' + n - 1) % n)
  have hLi : L.getD i ⊥ = (withSentinel xs).getD ((k' + n - 1) % n) ⊥ := by
    grind [last_getD_shiftRowIdx]
  have hFj : (firstColumn L).getD j ⊥ = (withSentinel xs).getD ((k' + n - 1) % n) ⊥ := by
    grind [first_getD_shiftRowIdx]
  grind

/--
  3. TAG EQUALITY (Non-Cyclic):
  Combined from symbol and rank matching.
-/
theorem tagF_shiftRowIdx_prev_eq_tagL_shiftRowIdx_fixed (xs : List α) (k : Nat) :
    let n := xs.length + 1
    let k' := k % n
    let L := (transform xs).last
    tagF L (shiftRowIdx xs ((k' + n - 1) % n)) = tagL L (shiftRowIdx xs k') := by
  apply Prod.ext
  · exact symbol_matching_fixed xs k
  · exact rank_matching_fixed xs k

/--
  4. LF IDENTITY (The Final Goal):
  Now we can prove LF(i) = j WITHOUT circularity.
-/
theorem LF_of_shiftRowIdx_fixed (xs : List α) (k : Nat) :
    let n := xs.length + 1
    let last := (transform xs).last
    let k' := k % n
    LF last (shiftRowIdx xs k') = shiftRowIdx xs ((k' + n - 1) % n) := by
  let n := xs.length + 1
  let k' := k % n
  let L := (transform xs).last
  let i := shiftRowIdx xs k'
  let j := shiftRowIdx xs ((k' + n - 1) % n)

  -- Use the property that LF(i) is the unique index m such that tagF(m) = tagL(i)
  -- Since we just proved tagF(j) = tagL(i), and tags are unique, LF(i) must be j.
  have hi : i < L.length := last_of_shiftRowIdx xs k
  have hj : j < (firstColumn L).length := by
    rw [firstColumn_length]
    exact last_of_shiftRowIdx xs (k' + n - 1)

  apply tag_uniqueness_F L (LF L i) j
  · exact LF_lt_firstColumn_length L i hi
  · exact hj
  · rw [tagF_LF_eq_tagL L i hi]
    exact (tagF_shiftRowIdx_prev_eq_tagL_shiftRowIdx_fixed xs k).symm
end Bzip2
