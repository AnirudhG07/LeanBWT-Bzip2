import Bzip2.Format.BZ2.Encoder
import Bzip2.Format.BZ2.Parser
import Bzip2.Correctness.BZ2.BitsReader
import Bzip2.Correctness.MTF

/-!
# Used-byte 16×16 bitmap roundtrip

The used-byte alphabet is serialized as a 16-bit "groups present" bitmap followed
by, for each present group, a 16-bit mask of which of its 16 bytes are used. This
module proves the decode inverts the encode for a sorted-nodup alphabet.

The combinatorial heart (this file's first half) is that testing bit `index` of a
mask built as a sum of distinct powers `Σ 2^(15-i)` recovers membership of `i`.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

/-! ### Sum-of-distinct-powers bit extraction -/

/-- A conditional-add left fold is the sum over the kept elements. -/
theorem foldl_cond_add (f : Nat → Nat) (P : Nat → Prop) [DecidablePred P] :
    ∀ (l : List Nat) (init : Nat),
      l.foldl (fun acc i => if P i then acc + f i else acc) init
        = init + ((l.filter (fun i => decide (P i))).map f).sum := by
  intro l
  induction l with
  | nil => intro init; simp
  | cons x xs ih =>
      intro init
      rw [List.foldl_cons, List.filter_cons]
      by_cases hx : P x
      · simp only [hx, if_pos, decide_true, List.map_cons, List.sum_cons, ih]
        omega
      · simp only [hx, if_neg, not_false_iff, decide_false, ih, Bool.false_eq_true]

/-- Adding two naturals with disjoint bits is bitwise-or at every position. -/
theorem testBit_add_of_disjoint : ∀ (k a b : Nat), a &&& b = 0 →
    (a + b).testBit k = (a.testBit k || b.testBit k) := by
  intro k
  induction k with
  | zero =>
      intro a b h
      have hkey : (a.testBit 0 && b.testBit 0) = false := by
        rw [← Nat.testBit_land, h, Nat.zero_testBit]
      rw [Nat.testBit_zero, Nat.testBit_zero] at hkey
      have hnb : a % 2 = 0 ∨ b % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
          rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp_all
      simp only [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp_all <;> omega
  | succ k ih =>
      intro a b h
      have hdisj : (a / 2) &&& (b / 2) = 0 := by
        apply Nat.eq_of_testBit_eq
        intro j
        have hkey : ((a / 2).testBit j && (b / 2).testBit j) = false := by
          rw [← Nat.testBit_succ, ← Nat.testBit_succ, ← Nat.testBit_land, h, Nat.zero_testBit]
        rw [Nat.testBit_land, Nat.zero_testBit]
        exact hkey
      have hkey0 : (a.testBit 0 && b.testBit 0) = false := by
        rw [← Nat.testBit_land, h, Nat.zero_testBit]
      rw [Nat.testBit_zero, Nat.testBit_zero] at hkey0
      have hnb : a % 2 = 0 ∨ b % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
          rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp_all
      have hdiv : (a + b) / 2 = a / 2 + b / 2 := by omega
      rw [Nat.testBit_succ, hdiv, ih (a / 2) (b / 2) hdisj, ← Nat.testBit_succ, ← Nat.testBit_succ]

/-- A single power disjoint from `b` exactly when `b`'s bit there is clear. -/
theorem two_pow_and_eq_zero (b e : Nat) (h : Nat.testBit b e = false) : 2 ^ e &&& b = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases hj : e = j
  · subst hj; simp [h]
  · simp [hj]

/-- Testing bit `p` of a sum of distinct powers of two recovers membership of the
exponent. -/
theorem testBit_sum_two_pow : ∀ (es : List Nat), es.Nodup → ∀ (p : Nat),
    Nat.testBit ((es.map (2 ^ ·)).sum) p = decide (p ∈ es) := by
  intro es
  induction es with
  | nil => intro _ p; simp
  | cons e es ih =>
      intro hnd p
      rw [List.nodup_cons] at hnd
      obtain ⟨hnotin, hnd'⟩ := hnd
      rw [List.map_cons, List.sum_cons]
      have hSe : ((es.map (2 ^ ·)).sum).testBit e = false := by
        rw [ih hnd' e]; simpa using hnotin
      rw [testBit_add_of_disjoint _ _ _ (two_pow_and_eq_zero _ _ hSe),
        Nat.testBit_two_pow, ih hnd' p]
      simp [List.mem_cons, eq_comm (a := p)]

/-- `bitSetFromLeft 16` is the `testBit` at the mirrored position. -/
theorem bitSetFromLeft_eq_testBit (value index : Nat) :
    bitSetFromLeft 16 value index = Nat.testBit value (15 - index) := by
  rw [bitSetFromLeft, Nat.testBit_eq_decide_div_mod_eq]

/-! ### Mask bit characterization -/

/-- Bit `k` of a `bitMaskAt`-weighted conditional fold over `range 16` records
exactly the predicate at `k`. -/
theorem fold_bitmap_bit (P : Nat → Prop) [DecidablePred P] (k : Nat) (hk : k < 16) :
    bitSetFromLeft 16
        ((List.range 16).foldl (fun acc i => if P i then acc + bitMaskAt i else acc) 0) k
      = decide (P k) := by
  rw [bitSetFromLeft_eq_testBit, foldl_cond_add]
  simp only [Nat.zero_add]
  rw [show ((List.range 16).filter (fun i => decide (P i))).map bitMaskAt
        = (((List.range 16).filter (fun i => decide (P i))).map (fun i => 15 - i)).map (2 ^ ·) from by
        rw [List.map_map]; apply List.map_congr_left; intro i _; rfl]
  rw [testBit_sum_two_pow _ ?nodup (15 - k)]
  case nodup =>
    apply List.Nodup.map_on
    · intro x hx y hy hxy
      rw [List.mem_filter, List.mem_range] at hx hy
      omega
    · exact (List.nodup_range).filter _
  rw [decide_eq_decide, List.mem_map]
  constructor
  · rintro ⟨i, hi, hik⟩
    rw [List.mem_filter, List.mem_range] at hi
    have : i = k := by omega
    subst this; simpa using hi.2
  · intro hPk
    exact ⟨k, by rw [List.mem_filter, List.mem_range]; exact ⟨hk, by simpa using hPk⟩, rfl⟩

/-- Bit `offset` of a group mask is set iff byte `group*16+offset` is used. -/
theorem groupMask_bit (group : Nat) (usedBytes : List UInt8) (offset : Nat) (hoff : offset < 16) :
    bitSetFromLeft 16 (groupMask group usedBytes) offset
      = decide (UInt8.ofNat (group * 16 + offset) ∈ usedBytes) := by
  rw [groupMask]
  exact fold_bitmap_bit (fun o => UInt8.ofNat (group * 16 + o) ∈ usedBytes) offset hoff

/-- Bit `group` of the groups bitmap is set iff that group's mask is nonzero. -/
theorem groupsBitmap_bit (usedBytes : List UInt8) (group : Nat) (hg : group < 16) :
    bitSetFromLeft 16 (groupsBitmap usedBytes) group
      = decide (groupMask group usedBytes ≠ 0) := by
  rw [groupsBitmap]
  rw [show (fun acc g => if groupMask g usedBytes = 0 then acc else acc + bitMaskAt g)
        = (fun acc g => if groupMask g usedBytes ≠ 0 then acc + bitMaskAt g else acc) from by
        funext acc g; by_cases h : groupMask g usedBytes = 0 <;> simp [h]]
  exact fold_bitmap_bit (fun g => groupMask g usedBytes ≠ 0) group hg

/-- The mirrored exponents of the kept offsets are distinct. -/
theorem filtered_mirror_nodup (P : Nat → Prop) [DecidablePred P] :
    (((List.range 16).filter (fun j => decide (P j))).map (fun j => 15 - j)).Nodup := by
  apply List.Nodup.map_on
  · intro x hx y hy hxy
    rw [List.mem_filter, List.mem_range] at hx hy
    omega
  · exact (List.nodup_range).filter _

/-- The mask sum fits in 16 bits. -/
theorem fold_bitmap_lt (P : Nat → Prop) [DecidablePred P] :
    (List.range 16).foldl (fun acc i => if P i then acc + bitMaskAt i else acc) 0 < 2 ^ 16 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [foldl_cond_add]
  simp only [Nat.zero_add]
  rw [show ((List.range 16).filter (fun i => decide (P i))).map bitMaskAt
        = (((List.range 16).filter (fun i => decide (P i))).map (fun i => 15 - i)).map (2 ^ ·) from by
        rw [List.map_map]; apply List.map_congr_left; intro i _; rfl]
  rw [testBit_sum_two_pow _ (filtered_mirror_nodup P) i]
  simp only [decide_eq_false_iff_not, List.mem_map, List.mem_filter, List.mem_range]
  rintro ⟨a, ⟨ha, _⟩, hai⟩
  omega

theorem groupMask_lt (group : Nat) (usedBytes : List UInt8) : groupMask group usedBytes < 2 ^ 16 := by
  rw [groupMask]; exact fold_bitmap_lt _

theorem groupsBitmap_lt (usedBytes : List UInt8) : groupsBitmap usedBytes < 2 ^ 16 := by
  rw [groupsBitmap,
    show (fun acc g => if groupMask g usedBytes = 0 then acc else acc + bitMaskAt g)
        = (fun acc g => if groupMask g usedBytes ≠ 0 then acc + bitMaskAt g else acc) from by
        funext acc g; by_cases h : groupMask g usedBytes = 0 <;> simp [h]]
  exact fold_bitmap_lt _

/-- The used bytes of one group, in ascending order — what the parser emits. -/
def groupUsedBytes (group : Nat) (usedBytes : List UInt8) : List UInt8 :=
  (List.range 16).filterMap (fun offset =>
    if UInt8.ofNat (group * 16 + offset) ∈ usedBytes then some (UInt8.ofNat (group * 16 + offset))
    else none)

/-- The parser's per-group `filterMap` over the mask equals that group's used bytes. -/
theorem parse_groupBytes (group : Nat) (usedBytes : List UInt8) :
    (List.range 16).filterMap (fun offset =>
        if bitSetFromLeft 16 (groupMask group usedBytes) offset then
          some (UInt8.ofNat (group * 16 + offset)) else none)
      = groupUsedBytes group usedBytes := by
  rw [groupUsedBytes]
  apply List.filterMap_congr
  intro offset hoff
  rw [List.mem_range] at hoff
  rw [groupMask_bit group usedBytes offset hoff]
  simp

/-- An empty group mask means the group contributes no bytes. -/
theorem groupMask_zero_groupUsedBytes (group : Nat) (usedBytes : List UInt8)
    (h : groupMask group usedBytes = 0) : groupUsedBytes group usedBytes = [] := by
  rw [groupUsedBytes, List.filterMap_eq_nil_iff]
  intro offset hoff
  rw [List.mem_range] at hoff
  have hbit := groupMask_bit group usedBytes offset hoff
  rw [h] at hbit
  have hmem : ¬ (UInt8.ofNat (group * 16 + offset) ∈ usedBytes) := by
    intro hmem
    rw [decide_eq_true hmem, bitSetFromLeft] at hbit
    simp at hbit
  rw [if_neg hmem]

/-- Sorted nodup lists with the same members are equal. -/
theorem sorted_nodup_ext (l₁ l₂ : List UInt8) (h1 : l₁.Pairwise (· ≤ ·)) (h2 : l₂.Pairwise (· ≤ ·))
    (hn1 : l₁.Nodup) (hn2 : l₂.Nodup) (hm : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ :=
  List.eq_of_perm_of_sorted (fun _ _ _ _ hab hba => UInt8.le_antisymm hab hba) h1 h2
    ((List.perm_ext_iff_of_nodup hn1 hn2).mpr hm)

/-! ### Writer bits and parser threading -/

/-- Bits emitted for the per-group masks. -/
def maskBits (us : List UInt8) : List Bool :=
  (List.range 16).flatMap (fun g => if groupMask g us = 0 then [] else natBitsMSB 16 (groupMask g us))

theorem writeMasks_bits (us : List UInt8) (gs : List Nat) :
    ∀ (w : BitWriter), w.WF →
      (gs.foldl (fun w g => if groupMask g us = 0 then w else w.writeBits 16 (groupMask g us)) w).bits
        = w.bits ++ gs.flatMap (fun g => if groupMask g us = 0 then [] else natBitsMSB 16 (groupMask g us))
      ∧ (gs.foldl (fun w g => if groupMask g us = 0 then w else w.writeBits 16 (groupMask g us)) w).WF := by
  induction gs with
  | nil => intro w hw; simp [hw]
  | cons g gs ih =>
      intro w hw
      rw [List.foldl_cons, List.flatMap_cons]
      by_cases hz : groupMask g us = 0
      · simp only [hz, if_pos, List.nil_append]
        obtain ⟨hb, hwf⟩ := ih w hw
        exact ⟨by rw [hb], hwf⟩
      · simp only [hz, if_neg, not_false_iff]
        obtain ⟨hb, hwf⟩ := ih (w.writeBits 16 (groupMask g us)) (w.writeBits_WF hw 16 _)
        refine ⟨?_, hwf⟩
        rw [hb, w.writeBits_bits hw 16 (groupMask g us), List.append_assoc]

theorem writeUsedBytes_bits (w : BitWriter) (hw : w.WF) (us : List UInt8) :
    (writeUsedBytes w us).bits = w.bits ++ natBitsMSB 16 (groupsBitmap us) ++ maskBits us := by
  rw [writeUsedBytes, maskBits]
  obtain ⟨hb, _⟩ :=
    writeMasks_bits us (List.range 16) (w.writeBits 16 (groupsBitmap us))
      (w.writeBits_WF hw 16 (groupsBitmap us))
  rw [hb, w.writeBits_bits hw 16 (groupsBitmap us), List.append_assoc]

/-- The parser consumes the per-group masks and reconstructs the per-group bytes. -/
theorem parseUsedBytesAux_spec (us : List UInt8) :
    ∀ (fuel group : Nat) (reader : BitReader) (acc : List UInt8) (rest : List Bool),
      group + fuel = 16 →
      (bitListOf reader.bytes).drop reader.bitPos
        = ((List.range' group fuel).flatMap
            (fun g => if groupMask g us = 0 then [] else natBitsMSB 16 (groupMask g us))) ++ rest →
      ∃ reader', parseUsedBytesAux fuel group (groupsBitmap us) reader acc
          = .ok (acc ++ (List.range' group fuel).flatMap (fun g => groupUsedBytes g us), reader')
        ∧ reader'.bytes = reader.bytes
        ∧ (bitListOf reader'.bytes).drop reader'.bitPos = rest := by
  intro fuel
  induction fuel with
  | zero =>
      intro group reader acc rest _ hpre
      refine ⟨reader, ?_, rfl, by simpa using hpre⟩
      simp only [parseUsedBytesAux, List.range'_zero, List.flatMap_nil, List.append_nil]
      rfl
  | succ fuel ih =>
      intro group reader acc rest hgf hpre
      have hg16 : group < 16 := by omega
      rw [List.range'_succ, List.flatMap_cons] at hpre ⊢
      rw [parseUsedBytesAux]
      have hbit : bitSetFromLeft 16 (groupsBitmap us) group = decide (groupMask group us ≠ 0) :=
        groupsBitmap_bit us group hg16
      by_cases hz : groupMask group us = 0
      · rw [hbit, if_neg (by simp [hz])]
        rw [if_pos hz, List.nil_append] at hpre
        rw [groupMask_zero_groupUsedBytes group us hz, List.nil_append]
        exact ih (group + 1) reader acc rest (by omega) hpre
      · rw [hbit, if_pos (decide_eq_true hz)]
        rw [if_neg hz] at hpre
        obtain ⟨hr16, hrem16⟩ :=
          readBits_of_prefix reader 16 (groupMask group us)
            ((List.range' (group + 1) fuel).flatMap
              (fun g => if groupMask g us = 0 then [] else natBitsMSB 16 (groupMask g us)) ++ rest)
            (groupMask_lt group us) hpre
        simp only [hr16, bind, Except.bind, parse_groupBytes]
        obtain ⟨reader', hpar, hbytes, hrem⟩ :=
          ih (group + 1) { reader with bitPos := reader.bitPos + 16 }
            (acc ++ groupUsedBytes group us) rest (by omega) (by simpa using hrem16)
        refine ⟨reader', ?_, by rw [hbytes], hrem⟩
        rw [hpar, List.append_assoc]

/-- The byte alphabet the parser reconstructs: every used byte, ascending. -/
def reconstruct (us : List UInt8) : List UInt8 :=
  (List.range 16).flatMap (fun g => groupUsedBytes g us)

/-- **The used-byte bitmap parser inverts the writer (up to reconstruction).** -/
theorem parseUsedBytes_of_prefix (us : List UInt8) (reader : BitReader) (rest : List Bool)
    (hpre : (bitListOf reader.bytes).drop reader.bitPos
              = natBitsMSB 16 (groupsBitmap us) ++ maskBits us ++ rest) :
    ∃ reader', parseUsedBytes reader = .ok (reconstruct us, reader')
      ∧ reader'.bytes = reader.bytes
      ∧ (bitListOf reader'.bytes).drop reader'.bitPos = rest := by
  rw [parseUsedBytes]
  obtain ⟨hr16, hrem16⟩ :=
    readBits_of_prefix reader 16 (groupsBitmap us) (maskBits us ++ rest) (groupsBitmap_lt us)
      (by rw [List.append_assoc] at hpre; exact hpre)
  simp only [hr16, bind, Except.bind]
  obtain ⟨reader', hpar, hbytes, hrem⟩ :=
    parseUsedBytesAux_spec us 16 0 { reader with bitPos := reader.bitPos + 16 } [] rest (by omega)
      (by simpa [maskBits, List.range_eq_range'] using hrem16)
  refine ⟨reader', ?_, by rw [hbytes], hrem⟩
  rw [hpar, reconstruct, List.range_eq_range', List.nil_append]

/-! ### Reconstruction equals the sorted alphabet -/

set_option maxRecDepth 4000 in
private theorem range_16_16_decomp :
    (List.range 16).flatMap (fun g => (List.range 16).map (fun off => g * 16 + off))
      = List.range 256 := by decide

private theorem filterMap_if_some {α : Type} (P : Nat → Prop) [DecidablePred P] (f : Nat → α)
    (l : List Nat) :
    l.filterMap (fun n => if P n then some (f n) else none)
      = (l.filter (fun n => decide (P n))).map f := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.filterMap_cons, List.filter_cons]
      by_cases hx : P x <;> simp [hx, ih]

/-- The reconstruction is the ascending list of every byte in the alphabet. -/
theorem reconstruct_eq_filter (us : List UInt8) :
    reconstruct us
      = ((List.range 256).filter (fun n => decide (UInt8.ofNat n ∈ us))).map UInt8.ofNat := by
  rw [reconstruct]
  have hg : ∀ g, groupUsedBytes g us
      = ((List.range 16).map (fun off => g * 16 + off)).filterMap
          (fun n => if UInt8.ofNat n ∈ us then some (UInt8.ofNat n) else none) := by
    intro g; rw [groupUsedBytes, List.filterMap_map]; rfl
  simp only [hg]
  rw [← List.filterMap_flatMap, range_16_16_decomp,
    filterMap_if_some (fun n => UInt8.ofNat n ∈ us) UInt8.ofNat]

/-- The reconstruction contains exactly the alphabet's bytes. -/
theorem mem_reconstruct (us : List UInt8) (b : UInt8) : b ∈ reconstruct us ↔ b ∈ us := by
  rw [reconstruct_eq_filter, List.mem_map]
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [List.mem_filter] at hn
    simpa using hn.2
  · intro hb
    refine ⟨b.toNat, ?_, by simp⟩
    rw [List.mem_filter, List.mem_range]
    exact ⟨UInt8.toNat_lt_size b, by simpa using hb⟩

/-- **Used-byte map round trip.** For a sorted-nodup alphabet, the reconstruction
equals it. -/
theorem reconstruct_eq (us : List UInt8) (hs : us.Pairwise (· ≤ ·)) (hn : us.Nodup) :
    reconstruct us = us := by
  refine sorted_nodup_ext _ _ ?_ hs ?_ hn (mem_reconstruct us)
  · rw [reconstruct_eq_filter, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ ((List.pairwise_lt_range).filter _)
    intro a b ha hb hab
    rw [List.mem_filter, List.mem_range] at ha hb
    rw [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat_of_lt' ha.1, UInt8.toNat_ofNat_of_lt' hb.1]
    omega
  · rw [reconstruct_eq_filter]
    apply List.Nodup.map_on
    · intro x hx y hy hxy
      rw [List.mem_filter, List.mem_range] at hx hy
      have h := congrArg UInt8.toNat hxy
      rw [UInt8.toNat_ofNat_of_lt' hx.1, UInt8.toNat_ofNat_of_lt' hy.1] at h
      exact h
    · exact (List.nodup_range).filter _

/-- The encoder's `usedBytes` alphabet is ascending. -/
theorem usedBytes_pairwise (input : ByteArray) : (usedBytes input).Pairwise (· ≤ ·) := by
  rw [usedBytes]; exact List.pairwise_mergeSort' _ _

/-- The encoder's `usedBytes` alphabet has no duplicates. -/
theorem usedBytes_nodup (input : ByteArray) : (usedBytes input).Nodup := by
  rw [usedBytes]; exact List.nodup_mergeSort.mpr (Bzip2.nodup_eraseDups _)

/-- **Used-byte map round trip (headline).** Parsing the bits the encoder wrote for
a sorted-nodup alphabet recovers exactly that alphabet. -/
theorem parseUsedBytes_roundtrip (us : List UInt8) (hs : us.Pairwise (· ≤ ·)) (hn : us.Nodup)
    (reader : BitReader) (rest : List Bool)
    (hpre : (bitListOf reader.bytes).drop reader.bitPos
              = natBitsMSB 16 (groupsBitmap us) ++ maskBits us ++ rest) :
    ∃ reader', parseUsedBytes reader = .ok (us, reader')
      ∧ reader'.bytes = reader.bytes ∧ (bitListOf reader'.bytes).drop reader'.bitPos = rest := by
  obtain ⟨r', hp, hb, hr⟩ := parseUsedBytes_of_prefix us reader rest hpre
  exact ⟨r', by rw [hp, reconstruct_eq us hs hn], hb, hr⟩

end Bzip2.Format.BZ2
