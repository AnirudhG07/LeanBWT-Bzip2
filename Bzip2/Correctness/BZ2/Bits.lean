import Bzip2.Format.BZ2.BitWriter
import Bzip2.Format.BZ2.BitReader

/-!
# Bit-layer correctness for the exact `.bz2` codec

This module gives the big-endian `BitWriter` a denotation as the `List Bool`
of bits it has emitted, and proves that `writeBit`/`writeBits` append exactly
the expected bits. These are the foundation on which every exact-format
parse/serialize agreement is built: the writer is characterised by the bit
list it produces, and the reader is characterised positionally over the same
bits.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

/-- The bit of `value` at position `i` (0 = least significant), as a `Bool`.
Uses `decide` to match the `BitWriter`/`BitReader` coercion of `· = 1`. -/
def natBit (value i : Nat) : Bool := decide ((value / 2 ^ i) % 2 = 1)

/-- The `count` low bits of `value`, most-significant bit first. -/
def natBitsMSB : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, v => natBit v n :: natBitsMSB n v

@[simp] theorem natBitsMSB_zero (v : Nat) : natBitsMSB 0 v = [] := rfl

theorem natBitsMSB_succ (n v : Nat) :
    natBitsMSB (n + 1) v = natBit v n :: natBitsMSB n v := rfl

@[simp] theorem natBitsMSB_length (n v : Nat) : (natBitsMSB n v).length = n := by
  induction n generalizing v with
  | zero => simp [natBitsMSB]
  | succ n ih => simp [natBitsMSB_succ, ih]

/-- Appending the least-significant bit at the end. -/
theorem natBitsMSB_snoc (n cb b : Nat) (hb : b < 2) :
    natBitsMSB (n + 1) (cb * 2 + b) = natBitsMSB n cb ++ [decide (b = 1)] := by
  induction n generalizing cb with
  | zero =>
      simp only [natBitsMSB_succ, natBitsMSB_zero, natBit, pow_zero, Nat.div_one, List.nil_append]
      have hmod : (cb * 2 + b) % 2 = b := by omega
      rw [hmod]
  | succ n ih =>
      have hdiv : (cb * 2 + b) / 2 ^ (n + 1) = cb / 2 ^ n := by
        have e : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
        rw [e, ← Nat.div_div_eq_div_mul]
        congr 1
        omega
      rw [natBitsMSB_succ, natBit, hdiv, ih, natBitsMSB_succ, natBit, List.cons_append]

/-- The eight bits of one output byte, most-significant bit first. -/
def byteBits (b : UInt8) : List Bool := natBitsMSB 8 b.toNat

/-- All bits written so far: completed bytes (in order) followed by the partial byte. -/
def BitWriter.bits (w : BitWriter) : List Bool :=
  (w.bytesRev.reverse.flatMap byteBits) ++ natBitsMSB w.usedBits w.currentByte

/-- Structural invariant: the partial byte holds fewer than 8 valid bits. -/
def BitWriter.WF (w : BitWriter) : Prop :=
  w.usedBits < 8 ∧ w.currentByte < 2 ^ w.usedBits

theorem BitWriter.empty_WF : BitWriter.empty.WF := by
  constructor <;> simp [BitWriter.empty]

@[simp] theorem BitWriter.empty_bits : BitWriter.empty.bits = [] := by
  simp [BitWriter.bits, BitWriter.empty]

/-- `writeBit` when the partial byte fills up (flush). -/
theorem BitWriter.writeBit_flush {w : BitWriter} {b : Bool} (hf : w.usedBits + 1 = 8) :
    w.writeBit b =
      { bytesRev := UInt8.ofNat (w.currentByte * 2 + (if b then 1 else 0)) :: w.bytesRev
      , currentByte := 0, usedBits := 0 } := by
  unfold BitWriter.writeBit; simp [hf]

/-- `writeBit` when the partial byte still has room. -/
theorem BitWriter.writeBit_noflush {w : BitWriter} {b : Bool} (hf : w.usedBits + 1 ≠ 8) :
    w.writeBit b =
      { w with currentByte := w.currentByte * 2 + (if b then 1 else 0)
             , usedBits := w.usedBits + 1 } := by
  unfold BitWriter.writeBit; simp [hf]

/-- `writeBit` preserves the well-formedness invariant. -/
theorem BitWriter.writeBit_WF {w : BitWriter} (h : w.WF) (b : Bool) :
    (w.writeBit b).WF := by
  obtain ⟨hlt, hcb⟩ := h
  by_cases hf : w.usedBits + 1 = 8
  · rw [writeBit_flush hf]
    simp [BitWriter.WF]
  · rw [writeBit_noflush hf]
    refine ⟨by simp only []; omega, ?_⟩
    simp only []
    have e : 2 ^ (w.usedBits + 1) = 2 * 2 ^ w.usedBits := by rw [pow_succ]; ring
    rw [e]
    rcases b with _ | _ <;> simp <;> omega

/-- `writeBit` appends exactly one bit to the writer's denotation. -/
theorem BitWriter.writeBit_bits {w : BitWriter} (h : w.WF) (b : Bool) :
    (w.writeBit b).bits = w.bits ++ [b] := by
  obtain ⟨hlt, hcb⟩ := h
  by_cases hf : w.usedBits + 1 = 8
  · -- flushing case: usedBits + 1 = 8
    have hused : w.usedBits = 7 := by omega
    rw [writeBit_flush hf]
    unfold BitWriter.bits
    simp only [List.reverse_cons, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, natBitsMSB_zero, List.append_assoc]
    congr 1
    have hbnd : w.currentByte * 2 + (if b then 1 else 0) < 256 := by
      rw [hused] at hcb; rcases b with _ | _ <;> simp_all <;> omega
    show byteBits (UInt8.ofNat (w.currentByte * 2 + if b then 1 else 0)) =
      natBitsMSB w.usedBits w.currentByte ++ [b]
    unfold byteBits
    rw [UInt8.toNat_ofNat_of_lt' hbnd, hused]
    have := natBitsMSB_snoc 7 w.currentByte (if b then 1 else 0) (by rcases b <;> simp)
    rw [show (8 : Nat) = 7 + 1 from rfl, this]
    congr 1
    rcases b with _ | _ <;> simp
  · -- non-flushing case
    rw [writeBit_noflush hf]
    simp only [BitWriter.bits, List.append_assoc]
    congr 1
    have := natBitsMSB_snoc w.usedBits w.currentByte (if b then 1 else 0) (by rcases b <;> simp)
    rw [this]
    congr 1
    rcases b with _ | _ <;> simp

/-- `writeBitsAux` appends the most-significant-first bits of `value`. -/
theorem BitWriter.writeBitsAux_bits {w : BitWriter} (h : w.WF) (count value : Nat) :
    (writeBitsAux count value w).bits = w.bits ++ natBitsMSB count value
      ∧ (writeBitsAux count value w).WF := by
  induction count generalizing w with
  | zero => exact ⟨by simp [writeBitsAux], h⟩
  | succ n ih =>
      rw [show writeBitsAux (n + 1) value w
            = writeBitsAux n value (w.writeBit (decide ((value / 2 ^ n) % 2 = 1))) from rfl]
      have hWF := w.writeBit_WF h (decide ((value / 2 ^ n) % 2 = 1))
      obtain ⟨ihbits, ihWF⟩ := ih hWF
      refine ⟨?_, ihWF⟩
      rw [ihbits, w.writeBit_bits h, natBitsMSB_succ, natBit]
      simp [List.append_assoc]

/-- `writeBits` appends exactly `natBitsMSB count value`. -/
theorem BitWriter.writeBits_bits {w : BitWriter} (h : w.WF) (count value : Nat) :
    (w.writeBits count value).bits = w.bits ++ natBitsMSB count value :=
  (BitWriter.writeBitsAux_bits h count value).1

theorem BitWriter.writeBits_WF {w : BitWriter} (h : w.WF) (count value : Nat) :
    (w.writeBits count value).WF :=
  (BitWriter.writeBitsAux_bits h count value).2

/-- `writeRepeatedBit` appends `count` copies of the bit. -/
theorem BitWriter.writeRepeatedBit_bits {w : BitWriter} (h : w.WF) (count : Nat) (b : Bool) :
    (w.writeRepeatedBit count b).bits = w.bits ++ List.replicate count b
      ∧ (w.writeRepeatedBit count b).WF := by
  induction count generalizing w with
  | zero => exact ⟨by simp [BitWriter.writeRepeatedBit], h⟩
  | succ n ih =>
      rw [show w.writeRepeatedBit (n + 1) b = (w.writeBit b).writeRepeatedBit n b from rfl]
      obtain ⟨ihbits, ihWF⟩ := ih (w.writeBit_WF h b)
      refine ⟨?_, ihWF⟩
      rw [ihbits, w.writeBit_bits h]
      simp [List.replicate_succ, List.append_assoc]

end Bzip2.Format.BZ2
