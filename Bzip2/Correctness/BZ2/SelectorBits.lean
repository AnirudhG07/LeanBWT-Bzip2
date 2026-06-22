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
  intro idxs
  induction idxs with
  | nil =>
      intro mtf acc reader rest result _ hdec hpre
      rw [decodeSelectorsAux, Except.ok.injEq] at hdec
      subst hdec
      refine ⟨reader, ?_, rfl, by simpa [selectorBits] using hpre⟩
      simp only [List.length_nil, parseSelectorsAux]
      rfl
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

/-- Every encoded selector index is a valid group index. -/
theorem encodeSelectorsAux_lt (gc : Nat) :
    ∀ (selectors mtf accE idxs : List Nat),
      mtf.length = gc → (∀ s ∈ selectors, s ∈ mtf) → (∀ i ∈ accE, i < gc) →
      encodeSelectorsAux selectors mtf accE = .ok idxs → ∀ i ∈ idxs, i < gc := by
  intro selectors
  induction selectors with
  | nil =>
      intro mtf accE idxs _ _ haccE henc
      simp only [encodeSelectorsAux, pure, Except.pure, Except.ok.injEq] at henc
      subst henc
      intro i hi; rw [List.mem_reverse] at hi; exact haccE i hi
  | cons s rest ih =>
      intro mtf accE idxs hlen hmem haccE henc
      have hs : s ∈ mtf := hmem s (by simp)
      have hpos : 1 ≤ mtf.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hs)
      have hmtfv : moveToFrontValue s mtf = .ok (mtf.findIdx (· = s), s :: mtf.erase s) := by
        simp only [moveToFrontValue, mtf_findIdx_getElem? s mtf hs]; rfl
      rw [encodeSelectorsAux, hmtfv] at henc
      simp only [bind, Except.bind] at henc
      have hfind : mtf.findIdx (· = s) < gc := by
        rw [← hlen]; exact List.findIdx_lt_length_of_exists ⟨s, hs, by simp⟩
      have hlen' : (s :: mtf.erase s).length = gc := by
        rw [List.length_cons, List.length_erase_of_mem hs]; omega
      have haccE' : ∀ i ∈ (mtf.findIdx (· = s) :: accE), i < gc := by
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact hfind
        · exact haccE i hi
      exact ih (s :: mtf.erase s) (mtf.findIdx (· = s) :: accE) idxs hlen'
        (fun x hx => mem_moveToFront (hmem x (by simp [hx]))) haccE' henc

/-- **Full on-the-wire selector round trip.** Parsing the unary-coded selector
indices the encoder wrote recovers the original selectors. -/
theorem parseSelectors_roundtrip (gc : Nat) (hgc : gc ≤ 64) (selectors idxs : List Nat)
    (hvalid : ∀ s ∈ selectors, s < gc) (henc : encodeSelectors gc selectors = .ok idxs)
    (reader : BitReader) (rest : List Bool)
    (hpre : (bitListOf reader.bytes).drop reader.bitPos = selectorBits idxs ++ rest) :
    ∃ reader', parseSelectorsAux idxs.length gc reader (List.range gc) [] = .ok (selectors, reader')
      ∧ reader'.bytes = reader.bytes
      ∧ (bitListOf reader'.bytes).drop reader'.bitPos = rest := by
  have hmem : ∀ s ∈ selectors, s ∈ List.range gc := fun s hs => List.mem_range.mpr (hvalid s hs)
  rw [encodeSelectors] at henc
  have hidxlt : ∀ i ∈ idxs, i < gc :=
    encodeSelectorsAux_lt gc selectors (List.range gc) [] idxs List.length_range hmem
      (by simp) henc
  have hdec : decodeSelectorsAux idxs (List.range gc) [] = .ok selectors := by
    have hd := decodeSelectors_encodeSelectors gc selectors hvalid idxs (by rw [encodeSelectors]; exact henc)
    rwa [decodeSelectors] at hd
  exact parseSelectorsAux_of_prefix gc hgc idxs (List.range gc) [] reader rest selectors hidxlt hdec hpre

end Bzip2.Format.BZ2
