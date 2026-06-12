import Bzip2.Format.BZ2.Encoder
import Bzip2.Format.BZ2.Parser
import Bzip2.Correctness.BZ2.BitsReader
import Bzip2.Correctness.BZ2.Selectors

/-!
# Selector unary bit coding roundtrip

Each move-to-front selector index is written in unary as `count` one-bits
terminated by a zero (`writeUnaryZeroTerminated`); the parser counts ones until a
zero (`parseUnaryIndexAux`). This module proves the unary coding round-trips at
the bit level via the `BitsReader` bridge, and composes with the selector
move-to-front roundtrip (`Selectors.lean`) to give the full on-the-wire selector
round trip.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

/-! ### Unary code -/

/-- `writeUnaryZeroTerminated` emits `count` ones then a zero. -/
theorem writeUnaryZeroTerminated_bits (w : BitWriter) (hw : w.WF) (count : Nat) :
    (writeUnaryZeroTerminated w count).bits = w.bits ++ List.replicate count true ++ [false]
      ∧ (writeUnaryZeroTerminated w count).WF := by
  rw [writeUnaryZeroTerminated]
  obtain ⟨hrep, hrepwf⟩ := w.writeRepeatedBit_bits hw count true
  refine ⟨?_, (w.writeRepeatedBit count true).writeBit_WF hrepwf false⟩
  rw [(w.writeRepeatedBit count true).writeBit_bits hrepwf false, hrep]

/-- The parser counts the unary ones and consumes the terminating zero. -/
theorem parseUnaryIndexAux_of_prefix (count : Nat) (rest : List Bool) :
    ∀ (fuel acc : Nat) (reader : BitReader),
      count < fuel →
      (bitListOf reader.bytes).drop reader.bitPos = List.replicate count true ++ false :: rest →
      ∃ reader', parseUnaryIndexAux fuel acc reader = .ok (acc + count, reader')
        ∧ reader'.bytes = reader.bytes
        ∧ (bitListOf reader'.bytes).drop reader'.bitPos = rest := by
  induction count with
  | zero =>
      intro fuel acc reader hf hpre
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [List.replicate_zero, List.nil_append] at hpre
      obtain ⟨hr, hrem⟩ := readBit_of_prefix reader false rest hpre
      refine ⟨{ reader with bitPos := reader.bitPos + 1 }, ?_, rfl, hrem⟩
      rw [parseUnaryIndexAux, hr]
      rfl
  | succ n ih =>
      intro fuel acc reader hf hpre
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [List.replicate_succ, List.cons_append] at hpre
      obtain ⟨hr, hrem⟩ :=
        readBit_of_prefix reader true (List.replicate n true ++ false :: rest) hpre
      obtain ⟨reader', hp, hb, hrm⟩ :=
        ih f (acc + 1) { reader with bitPos := reader.bitPos + 1 } (by omega) (by simpa using hrem)
      refine ⟨reader', ?_, by rw [hb], hrm⟩
      rw [parseUnaryIndexAux, hr]
      simp only [bind, Except.bind, if_true]
      rw [hp]
      congr 2
      omega

/-! ### Full on-the-wire selector stream -/

/-- Bits emitted for a list of encoded selector indices. -/
def selectorBits (idxs : List Nat) : List Bool :=
  idxs.flatMap (fun i => List.replicate i true ++ [false])

/-- The encoder's selector fold emits exactly `selectorBits`. -/
theorem writeUnary_foldl_bits (idxs : List Nat) :
    ∀ (w : BitWriter), w.WF →
      (idxs.foldl writeUnaryZeroTerminated w).bits = w.bits ++ selectorBits idxs
      ∧ (idxs.foldl writeUnaryZeroTerminated w).WF := by
  induction idxs with
  | nil => intro w hw; simp [selectorBits, hw]
  | cons i is ih =>
      intro w hw
      rw [List.foldl_cons, selectorBits, List.flatMap_cons]
      obtain ⟨hb, hwf⟩ := writeUnaryZeroTerminated_bits w hw i
      obtain ⟨hb', hwf'⟩ := ih (writeUnaryZeroTerminated w i) hwf
      refine ⟨?_, hwf'⟩
      rw [hb', hb, selectorBits]
      simp [List.append_assoc]

/-- The parser consumes the unary indices and move-to-front-decodes them,
matching `decodeSelectorsAux`. -/
theorem parseSelectorsAux_of_prefix (gc : Nat) (hgc : gc ≤ 64) :
    ∀ (idxs : List Nat) (mtf acc : List Nat) (reader : BitReader) (rest : List Bool) (result : List Nat),
      (∀ i ∈ idxs, i < gc) →
      decodeSelectorsAux idxs mtf acc = .ok result →
      (bitListOf reader.bytes).drop reader.bitPos = selectorBits idxs ++ rest →
      ∃ reader', parseSelectorsAux idxs.length gc reader mtf acc = .ok (result, reader')
        ∧ reader'.bytes = reader.bytes
        ∧ (bitListOf reader'.bytes).drop reader'.bitPos = rest := by
  induction idxs with
  | nil =>
      intro mtf acc reader rest result _ hdec hpre
      rw [decodeSelectorsAux] at hdec
      refine ⟨reader, ?_, rfl, by simpa [selectorBits] using hpre⟩
      simp only [List.length_nil, parseSelectorsAux]
      rw [Except.ok.injEq] at hdec ⊢
      exact ⟨hdec, rfl⟩
  | cons i is ih =>
      intro mtf acc reader rest result hvalid hdec hpre
      have hi : i < gc := hvalid i (by simp)
      rw [selectorBits, List.flatMap_cons] at hpre
      simp only [List.append_assoc, List.singleton_append] at hpre
      -- read the unary index i
      obtain ⟨reader1, hr, hb1, hrem1⟩ :=
        parseUnaryIndexAux_of_prefix i (selectorBits is ++ rest) 64 0 reader (by omega) hpre
      -- analyse the move-to-front decode step
      rw [decodeSelectorsAux] at hdec
      cases hmtf : moveToFrontIndex i mtf with
      | error e => rw [hmtf] at hdec; simp [bind, Except.bind] at hdec
      | ok p =>
          obtain ⟨value, mtf'⟩ := p
          rw [hmtf] at hdec
          simp only [bind, Except.bind] at hdec
          obtain ⟨reader', hpar, hbytes, hrm⟩ :=
            ih mtf' (value :: acc) reader1 rest result (fun j hj => hvalid j (by simp [hj]))
              hdec hrem1
          refine ⟨reader', ?_, by rw [hbytes, hb1], hrm⟩
          rw [List.length_cons, parseSelectorsAux, parseUnaryIndex]
          simp only [hr, bind, Except.bind, Nat.zero_add, pure, Except.pure,
            if_neg (by omega : ¬ i ≥ gc), hmtf]
          rw [hpar]

end Bzip2.Format.BZ2
