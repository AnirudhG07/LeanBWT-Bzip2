import Bzip2.Correctness.LF

/-!
This file proves correctness of BWT inversion from the LF map. It shows that
iterating `lfCollect` walks backward through the original cyclic string and
uses that to prove `inverse (transform xs) = xs`.
-/

set_option linter.unusedSectionVars false

namespace Bzip2

section LFCorrectness

set_option autoImplicit false

variable {α : Type} [LinearOrder α] [DecidableEq α]

/-- Closed-form index of the symbol read at step `i` of an LF walk. -/
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
          grind only [Nat.mod_eq_of_lt (Nat.lt_succ_self m)]
      | succ k =>
          have hk' : k < m + 1 := Nat.lt_of_succ_lt hk
          have hsimpl : (Nat.succ k + (m + 1) - 1 : Nat) = Nat.succ k + m := by grind only
          have hmod : (Nat.succ k + m) % (m + 1) = k := by
            have hsum : Nat.succ k + m = k + (m + 1) := by linarith
            calc
              (Nat.succ k + m) % (m + 1) = (k + (m + 1)) % (m + 1) := by
                rw [hsum]
              _ = k % (m + 1) := by rw [Nat.add_mod_right]
              _ = k := Nat.mod_eq_of_lt hk'
          rw [hsimpl, hmod]
          have hmul : m * (c + 2) = m * (c + 1) + m := by
            exact Nat.mul_succ m (c + 1)
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
      have hn : 0 < n := by simp [n]
      have hk_lt : k' < n := by exact Nat.mod_lt k hn
      have hstep : lfStep last (shiftRowIdx xs k') = shiftRowIdx xs next_k := by
        grind [LF_of_shiftRowIdx]
      have hnext_lt : next_k < n := by
        exact Nat.mod_lt (k' + n - 1) hn
      have ih' :
          (lfCollect last c (shiftRowIdx xs next_k)).reverse =
            (List.range c).map (fun i => (withSentinel xs).getD (lfCollectIdx n next_k c i) ⊥) := by
        simpa [n, last, next_k, Nat.mod_eq_of_lt hnext_lt] using (ih next_k)
      have hlast :
          last.getD (shiftRowIdx xs next_k) ⊥ = (withSentinel xs).getD ((next_k + n - 1) % n) ⊥ := by
        grind only [!last_getD_shiftRowIdx]
      have hlastOpt :
          last[shiftRowIdx xs next_k]?.getD ⊥ = (withSentinel xs).getD ((next_k + n - 1) % n) ⊥ := by
        grind only [= List.getD_eq_getElem?_getD]
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
        linarith
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

/-- Reconstructing from the BWT last column via LF returns the original input. -/
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
  grind only [inverse, inverseAlgorithmic, = inverseFromLast.eq_1]

/-- Public wrapper for the LF-based inverse-transform correctness theorem. -/
theorem inverse_transform (xs : List α) :
    inverse (transform xs) = xs := by
  exact inverse_transform_from_LF xs

end LFCorrectness

end Bzip2
