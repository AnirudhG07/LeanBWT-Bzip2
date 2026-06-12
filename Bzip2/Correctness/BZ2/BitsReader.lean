import Bzip2.Correctness.BZ2.Bits
import Bzip2.Correctness.BZ2.RLE1

/-!
# Bit-reader denotation for the exact `.bz2` codec

The `BitReader` is characterised positionally over the `List Bool` of bits of its
backing byte array (`bitListOf`, MSB-first per byte, matching the writer's
`byteBits`). `readBit` consumes the head bit at the cursor and `readBits count`
consumes `count` bits MSB-first. Combined with the writer side (`Bits.lean`) this
is the foundation for every parse/serialize round trip: the writer emits
`BitWriter.bits`, the reader consumes exactly those bits back.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

/-- Interpret a most-significant-first bit list as a natural number, matching
`readBitsAux`'s `acc * 2 + bit` accumulation. -/
def fromBitsMSB (bs : List Bool) : Nat :=
  bs.foldl (fun acc b => acc * 2 + if b then 1 else 0) 0

/-- All bits of a byte array, in order, MSB-first within each byte. -/
def bitListOf (ba : ByteArray) : List Bool :=
  ba.toList.flatMap byteBits

theorem flatMap_byteBits_length (l : List UInt8) :
    (l.flatMap byteBits).length = l.length * 8 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, byteBits,
        natBitsMSB_length, ih, Nat.succ_mul]
      omega

@[simp] theorem bitListOf_length (ba : ByteArray) : (bitListOf ba).length = ba.size * 8 := by
  rw [bitListOf, flatMap_byteBits_length, toList_eq, Array.length_toList]
  rfl

/-- Indexing into the MSB-first bits of a single value. -/
theorem natBitsMSB_getElem? (n v j : Nat) (hj : j < n) :
    (natBitsMSB n v)[j]? = some (natBit v (n - 1 - j)) := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
      rw [natBitsMSB_succ]
      match j with
      | 0 => simp
      | k + 1 =>
          rw [List.getElem?_cons_succ, ih k (by omega),
            show n + 1 - 1 - (k + 1) = n - 1 - k from by omega]

/-! ### Positional indexing of the bit list -/

/-- Position `p` of the flattened bit list selects bit `7 - p % 8` of byte
`p / 8`. -/
theorem flatMap_byteBits_getElem? (l : List UInt8) (p : Nat) (h : p < l.length * 8) :
    (l.flatMap byteBits)[p]? = some (natBit (l[p / 8]!).toNat (7 - p % 8)) := by
  induction l generalizing p with
  | nil => simp at h
  | cons x xs ih =>
      rw [List.flatMap_cons]
      have hlen : (byteBits x).length = 8 := by simp [byteBits]
      by_cases hp : p < 8
      · rw [List.getElem?_append_left (by omega)]
        rw [byteBits, natBitsMSB_getElem? 8 x.toNat p hp]
        have hpd : p / 8 = 0 := by omega
        have hpm : p % 8 = p := by omega
        rw [hpd, hpm]
        simp
      · rw [List.getElem?_append_right (by omega), hlen]
        have hlt : p - 8 < xs.length * 8 := by
          simp only [List.length_cons] at h; omega
        rw [ih (p - 8) hlt]
        have hpd : p / 8 = (p - 8) / 8 + 1 := by omega
        have hpm : (p - 8) % 8 = p % 8 := by omega
        rw [hpd, hpm]
        simp

theorem bitListOf_getElem? (ba : ByteArray) (p : Nat) (h : p < ba.size * 8) :
    (bitListOf ba)[p]? = some (natBit (ba.toList[p / 8]!).toNat (7 - p % 8)) := by
  rw [bitListOf, flatMap_byteBits_getElem? ba.toList p (by rwa [toList_eq, Array.length_toList])]

/-! ### Reader steps consume the bit list -/

/-- `readBit` returns the bit at the cursor (as positioned in `bitListOf`) and
advances by one. -/
theorem readBit_eq (r : BitReader) (h : r.bitPos < r.bytes.size * 8) :
    r.readBit = .ok ((bitListOf r.bytes)[r.bitPos]'(by simpa using h),
      { r with bitPos := r.bitPos + 1 }) := by
  have hb : (bitListOf r.bytes)[r.bitPos]'(by simpa using h)
      = natBit (r.bytes.toList[r.bitPos / 8]!).toNat (7 - r.bitPos % 8) := by
    have := bitListOf_getElem? r.bytes r.bitPos h
    rw [List.getElem?_eq_getElem (by simpa using h)] at this
    exact Option.some.inj this
  have hidx : r.bitPos / 8 < r.bytes.size := by omega
  have hbyte : r.bytes.toList[r.bitPos / 8]! = r.bytes[r.bitPos / 8]'hidx := by
    have hlen : r.bitPos / 8 < r.bytes.data.toList.length := by
      rw [Array.length_toList]; exact hidx
    simp only [toList_eq]
    rw [getElem!_pos r.bytes.data.toList (r.bitPos / 8) hlen, Array.getElem_toList,
      ByteArray.getElem_eq_data_getElem]
    rfl
  unfold BitReader.readBit
  rw [dif_pos h]
  simp only []
  rw [hb, hbyte]
  rfl

/-! ### Numeric round trip for `readBits` -/

theorem fromBitsMSB_foldl (bs : List Bool) (acc : Nat) :
    bs.foldl (fun a b => a * 2 + if b then 1 else 0) acc
      = acc * 2 ^ bs.length + fromBitsMSB bs := by
  induction bs generalizing acc with
  | nil => simp [fromBitsMSB]
  | cons b bs ih =>
      rw [List.foldl_cons, ih]
      conv_rhs => rw [fromBitsMSB, List.foldl_cons, ih]
      simp only [List.length_cons, pow_succ, Nat.zero_mul, Nat.zero_add]
      ring

theorem fromBitsMSB_cons (b : Bool) (bs : List Bool) :
    fromBitsMSB (b :: bs) = (if b then 1 else 0) * 2 ^ bs.length + fromBitsMSB bs := by
  rw [fromBitsMSB, List.foldl_cons, fromBitsMSB_foldl]
  simp

theorem fromBitsMSB_append_singleton (xs : List Bool) (x : Bool) :
    fromBitsMSB (xs ++ [x]) = fromBitsMSB xs * 2 + (if x then 1 else 0) := by
  unfold fromBitsMSB
  rw [List.foldl_append]
  simp

/-- Reading back the MSB-first bits of a value recovers it. -/
theorem fromBitsMSB_natBitsMSB (count : Nat) : ∀ value, value < 2 ^ count →
    fromBitsMSB (natBitsMSB count value) = value := by
  induction count with
  | zero => intro value h; interval_cases value; simp [natBitsMSB, fromBitsMSB]
  | succ count ih =>
      intro value h
      have hb : value % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hcb : value / 2 < 2 ^ count := by rw [pow_succ] at h; omega
      have key : natBitsMSB (count + 1) value
          = natBitsMSB count (value / 2) ++ [decide (value % 2 = 1)] := by
        conv_lhs => rw [← Nat.div_add_mod value 2]
        rw [show 2 * (value / 2) + value % 2 = (value / 2) * 2 + value % 2 from by ring]
        exact natBitsMSB_snoc count (value / 2) (value % 2) hb
      rw [key, fromBitsMSB_append_singleton, ih (value / 2) hcb]
      by_cases hm : value % 2 = 1 <;> simp [hm] <;> omega

/-! ### `readBits` consumes a value-prefix of the bit stream -/

theorem readBitsAux_eq (n : Nat) : ∀ (acc : Nat) (r : BitReader), n ≤ r.bitsRemaining →
    readBitsAux n acc r
      = .ok (acc * 2 ^ n + fromBitsMSB (((bitListOf r.bytes).drop r.bitPos).take n),
             { r with bitPos := r.bitPos + n }) := by
  induction n with
  | zero =>
      intro acc r _
      simp only [readBitsAux, pow_zero, Nat.mul_one, List.take_zero, fromBitsMSB,
        List.foldl_nil, Nat.add_zero]
      rfl
  | succ n ih =>
      intro acc r hrem
      have hpos : r.bitPos < r.bytes.size * 8 := by
        unfold BitReader.bitsRemaining at hrem; omega
      have hlen : r.bitPos < (bitListOf r.bytes).length := by simpa using hpos
      have hrem' : n ≤ ({ r with bitPos := r.bitPos + 1 } : BitReader).bitsRemaining := by
        show n ≤ r.bytes.size * 8 - (r.bitPos + 1)
        unfold BitReader.bitsRemaining at hrem; omega
      rw [readBitsAux, readBit_eq r hpos]
      show readBitsAux n (acc * 2 + if (bitListOf r.bytes)[r.bitPos]'hlen then 1 else 0)
            { r with bitPos := r.bitPos + 1 } = _
      rw [ih _ { r with bitPos := r.bitPos + 1 } hrem']
      -- assemble: peel the head bit of the drop
      have hdrop : (bitListOf r.bytes).drop r.bitPos
          = (bitListOf r.bytes)[r.bitPos]'hlen :: (bitListOf r.bytes).drop (r.bitPos + 1) :=
        List.drop_eq_getElem_cons hlen
      have htakelen : (((bitListOf r.bytes).drop (r.bitPos + 1)).take n).length = n := by
        rw [List.length_take, List.length_drop, bitListOf_length]
        unfold BitReader.bitsRemaining at hrem; omega
      rw [hdrop, List.take_succ_cons, fromBitsMSB_cons, htakelen]
      simp only [Except.ok.injEq, Prod.mk.injEq]
      refine ⟨?_, by congr 1; omega⟩
      rw [pow_succ]
      ring

theorem readBits_eq (r : BitReader) (count : Nat) (h : count ≤ r.bitsRemaining) :
    r.readBits count
      = .ok (fromBitsMSB (((bitListOf r.bytes).drop r.bitPos).take count),
             { r with bitPos := r.bitPos + count }) := by
  rw [BitReader.readBits, readBitsAux_eq count 0 r h]
  simp

/-- **Reader/writer bridge.** If the bits at the cursor begin with the MSB-first
encoding of `value` (`value < 2^count`), `readBits count` returns `value` and
advances past exactly those bits. -/
theorem readBits_of_prefix (r : BitReader) (count value : Nat) (rest : List Bool)
    (hval : value < 2 ^ count)
    (hpre : (bitListOf r.bytes).drop r.bitPos = natBitsMSB count value ++ rest) :
    r.readBits count = .ok (value, { r with bitPos := r.bitPos + count })
      ∧ (bitListOf r.bytes).drop (r.bitPos + count) = rest := by
  have hlenpre : ((bitListOf r.bytes).drop r.bitPos).length = count + rest.length := by
    rw [hpre]; simp
  have hcount : count ≤ r.bitsRemaining := by
    rw [List.length_drop, bitListOf_length] at hlenpre
    unfold BitReader.bitsRemaining; omega
  have htake : ((bitListOf r.bytes).drop r.bitPos).take count = natBitsMSB count value := by
    rw [hpre, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  refine ⟨?_, ?_⟩
  · rw [readBits_eq r count hcount, htake, fromBitsMSB_natBitsMSB count value hval]
  · rw [← List.drop_drop, hpre, List.drop_append_of_le_length (by simp)]
    simp

/-! ### Writer finalization bridge

Connects the finalized `ByteArray` of a `BitWriter` back to its `List Bool`
denotation, so every writer `.bits` lemma lifts to the reader side. -/

theorem byteArrayOfList_toList (xs : List UInt8) :
    (Bzip2.Format.byteArrayOfList xs).toList = xs := by
  rw [toList_eq]; simp [Bzip2.Format.byteArrayOfList]

theorem bitListOf_byteArrayOfList (xs : List UInt8) :
    bitListOf (Bzip2.Format.byteArrayOfList xs) = xs.flatMap byteBits := by
  rw [bitListOf, byteArrayOfList_toList]

theorem writeBit_usedBits (w : BitWriter) (h : w.WF) (b : Bool) :
    (w.writeBit b).usedBits = (w.usedBits + 1) % 8 := by
  obtain ⟨hlt, _⟩ := h
  by_cases hf : w.usedBits + 1 = 8
  · rw [BitWriter.writeBit_flush hf]; show (0 : Nat) = (w.usedBits + 1) % 8; omega
  · rw [BitWriter.writeBit_noflush hf]; show w.usedBits + 1 = (w.usedBits + 1) % 8; omega

theorem writeRepeatedBit_usedBits (w : BitWriter) (h : w.WF) (k : Nat) (b : Bool) :
    (w.writeRepeatedBit k b).usedBits = (w.usedBits + k) % 8 := by
  induction k generalizing w with
  | zero => have := h.1; simp only [BitWriter.writeRepeatedBit, Nat.add_zero]; omega
  | succ k ih =>
      rw [show w.writeRepeatedBit (k + 1) b = (w.writeBit b).writeRepeatedBit k b from rfl,
        ih (w.writeBit b) (w.writeBit_WF h b), writeBit_usedBits w h b]
      omega

theorem alignToByte_usedBits (w : BitWriter) (h : w.WF) : (w.alignToByte).usedBits = 0 := by
  have hlt := h.1
  by_cases hu : w.usedBits = 0
  · simp [BitWriter.alignToByte, BitWriter.isByteAligned, hu]
  · simp only [BitWriter.alignToByte, BitWriter.isByteAligned, hu, decide_false,
      Bool.false_eq_true, if_false]
    rw [writeRepeatedBit_usedBits w h (8 - w.usedBits) false]
    omega

theorem alignToByte_bits (w : BitWriter) (h : w.WF) :
    (w.alignToByte).bits = w.bits ++ List.replicate (if w.usedBits = 0 then 0 else 8 - w.usedBits) false := by
  by_cases hu : w.usedBits = 0
  · simp [BitWriter.alignToByte, BitWriter.isByteAligned, hu]
  · simp only [BitWriter.alignToByte, BitWriter.isByteAligned, hu, decide_false,
      Bool.false_eq_true, if_false]
    rw [(BitWriter.writeRepeatedBit_bits h (8 - w.usedBits) false).1]

theorem bitListOf_of_aligned (w : BitWriter) (h : w.usedBits = 0) :
    bitListOf (Bzip2.Format.byteArrayOfList w.bytesRev.reverse) = w.bits := by
  rw [bitListOf_byteArrayOfList]
  simp only [BitWriter.bits, h, natBitsMSB_zero, List.append_nil]

/-- **Writer finalization.** The bits of the finalized byte array are exactly the
writer's emitted bits, plus zero padding to the next byte boundary. -/
theorem bitListOf_toByteArray (w : BitWriter) (h : w.WF) :
    bitListOf (BitWriter.toByteArray w)
      = w.bits ++ List.replicate (if w.usedBits = 0 then 0 else 8 - w.usedBits) false := by
  unfold BitWriter.toByteArray
  rw [bitListOf_of_aligned _ (alignToByte_usedBits w h), alignToByte_bits w h]

/-- **Entry point for parse/serialize proofs.** A fresh reader over a finalized
writer sees, from its cursor, exactly the writer's emitted bits followed by the
end padding. Field round trips chain `readBits_of_prefix` from here. -/
theorem ofByteArray_toByteArray_remaining (w : BitWriter) (h : w.WF) :
    (bitListOf (BitReader.ofByteArray (BitWriter.toByteArray w)).bytes).drop
        (BitReader.ofByteArray (BitWriter.toByteArray w)).bitPos
      = w.bits ++ List.replicate (if w.usedBits = 0 then 0 else 8 - w.usedBits) false := by
  simp only [BitReader.ofByteArray, List.drop_zero]
  exact bitListOf_toByteArray w h

/-- Single-bit analogue of `readBits_of_prefix`: if the cursor bits begin with
`b`, `readBit` returns `b` and advances one position. -/
theorem readBit_of_prefix (r : BitReader) (b : Bool) (rest : List Bool)
    (hpre : (bitListOf r.bytes).drop r.bitPos = b :: rest) :
    r.readBit = .ok (b, { r with bitPos := r.bitPos + 1 })
      ∧ (bitListOf r.bytes).drop (r.bitPos + 1) = rest := by
  have hlen : r.bitPos < (bitListOf r.bytes).length := by
    have h0 : 0 < ((bitListOf r.bytes).drop r.bitPos).length := by rw [hpre]; simp
    rw [List.length_drop] at h0; omega
  have hpos : r.bitPos < r.bytes.size * 8 := by rwa [← bitListOf_length]
  have hcons := List.drop_eq_getElem_cons hlen
  rw [hpre] at hcons
  obtain ⟨hb, hrest⟩ := List.cons.inj hcons
  refine ⟨?_, hrest.symm⟩
  rw [readBit_eq r hpos, hb]
