import Bzip2.Format.BZ2.Encoder
import Bzip2.Format.BZ2.Parser
import Bzip2.Correctness.BZ2.BitsReader

/-!
# Huffman code-length delta-table roundtrip

A code-length table is serialized as a 5-bit start length followed by, for each
symbol, a unary delta walk (`writeLengthDelta`: a `(true, dir)` pair per ±1 step,
`dir = true` decrements) terminated by a `false` bit. The parser
(`parseOneLengthAux`) walks the same deltas. This module proves the per-symbol
delta walk round-trips at the bit level via the `BitsReader` bridge, then lifts
it to the full table.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

/-- The bits emitted by `writeLengthDelta` moving `current` to `target`:
a `(true, dir)` pair per ±1 step (`dir = true` for a decrement). -/
def deltaBits : Nat → Nat → List Bool
  | current, target =>
      if current = target then []
      else if target < current then true :: true :: deltaBits (current - 1) target
      else true :: false :: deltaBits (current + 1) target
termination_by current target => (current - target) + (target - current)
decreasing_by all_goals omega

/-- **`writeLengthDelta` emits exactly `deltaBits`** and preserves well-formedness. -/
theorem writeLengthDelta_bits (w : BitWriter) (h : w.WF) (current target : Nat) :
    (writeLengthDelta w current target).bits = w.bits ++ deltaBits current target
      ∧ (writeLengthDelta w current target).WF := by
  rw [writeLengthDelta, deltaBits]
  split
  · simp_all
  · have hb1 : (w.writeBit true).WF := w.writeBit_WF h true
    split
    · -- decrement
      have hb2 : ((w.writeBit true).writeBit true).WF := (w.writeBit true).writeBit_WF hb1 true
      obtain ⟨hbits, hwf⟩ := writeLengthDelta_bits ((w.writeBit true).writeBit true) hb2 (current - 1) target
      refine ⟨?_, hwf⟩
      rw [hbits, (w.writeBit true).writeBit_bits hb1 true, w.writeBit_bits h true]
      simp
    · -- increment
      have hb2 : ((w.writeBit true).writeBit false).WF := (w.writeBit true).writeBit_WF hb1 false
      obtain ⟨hbits, hwf⟩ := writeLengthDelta_bits ((w.writeBit true).writeBit false) hb2 (current + 1) target
      refine ⟨?_, hwf⟩
      rw [hbits, (w.writeBit true).writeBit_bits hb1 false, w.writeBit_bits h true]
      simp
termination_by (current - target) + (target - current)
decreasing_by all_goals omega

/-- **The parser walks back exactly `deltaBits`.** Reading from a cursor whose
bits begin with `deltaBits current target ++ false :: rest` recovers `target`,
leaving `rest`, provided both endpoints are in `[0, 20]` and fuel suffices. -/
theorem parseOneLengthAux_of_prefix (current target : Nat)
    (htarget : target ≤ 20) (hcurrent : current ≤ 20) (rest : List Bool) :
    ∀ (fuel : Nat) (reader : BitReader),
      (current - target) + (target - current) < fuel →
      (bitListOf reader.bytes).drop reader.bitPos = deltaBits current target ++ false :: rest →
      ∃ reader', parseOneLengthAux fuel current reader = .ok (target, reader')
        ∧ reader'.bytes = reader.bytes
        ∧ (bitListOf reader'.bytes).drop reader'.bitPos = rest := by
  intro fuel reader hfuel hpre
  obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  by_cases hct : current = target
  · -- terminate: deltaBits = [], next bit is the terminating `false`
    subst hct
    have hdb : deltaBits current current = [] := by rw [deltaBits]; simp
    rw [hdb, List.nil_append] at hpre
    obtain ⟨hread, hrem⟩ := readBit_of_prefix reader false rest hpre
    refine ⟨{ reader with bitPos := reader.bitPos + 1 }, ?_, rfl, hrem⟩
    rw [parseOneLengthAux, hread]
    rfl
  · by_cases hlt : target < current
    · -- decrement step
      have hdb : deltaBits current target
          = true :: true :: deltaBits (current - 1) target := by
        rw [deltaBits, if_neg hct, if_pos hlt]
      rw [hdb] at hpre
      -- read the two bits of the pair
      obtain ⟨hr1, hrem1⟩ :=
        readBit_of_prefix reader true (true :: deltaBits (current - 1) target ++ false :: rest) hpre
      obtain ⟨hr2, hrem2⟩ :=
        readBit_of_prefix { reader with bitPos := reader.bitPos + 1 } true
          (deltaBits (current - 1) target ++ false :: rest) hrem1
      have hadj : adjustCodeLength current true = .ok (current - 1) := by
        rw [adjustCodeLength, if_pos (by simp), if_neg (by omega : ¬ current = 0)]
        rfl
      -- recurse on current - 1
      obtain ⟨reader', hpar, hbytes', hrem'⟩ :=
        parseOneLengthAux_of_prefix (current - 1) target htarget (by omega) rest fuel'
          { reader with bitPos := reader.bitPos + 1 + 1 } (by omega)
          (by simpa using hrem2)
      refine ⟨reader', ?_, by rw [hbytes'], hrem'⟩
      rw [parseOneLengthAux]
      simp only [hr1, hr2, hadj, bind, Except.bind, if_true]
      exact hpar
    · -- increment step
      have hgt : current < target := by omega
      have hdb : deltaBits current target
          = true :: false :: deltaBits (current + 1) target := by
        rw [deltaBits, if_neg hct, if_neg hlt]
      rw [hdb] at hpre
      obtain ⟨hr1, hrem1⟩ :=
        readBit_of_prefix reader true (false :: deltaBits (current + 1) target ++ false :: rest) hpre
      obtain ⟨hr2, hrem2⟩ :=
        readBit_of_prefix { reader with bitPos := reader.bitPos + 1 } false
          (deltaBits (current + 1) target ++ false :: rest) hrem1
      have hadj : adjustCodeLength current false = .ok (current + 1) := by
        rw [adjustCodeLength, if_neg (by simp), if_neg (by omega : ¬ current = 20)]
        rfl
      obtain ⟨reader', hpar, hbytes', hrem'⟩ :=
        parseOneLengthAux_of_prefix (current + 1) target htarget (by omega) rest fuel'
          { reader with bitPos := reader.bitPos + 1 + 1 } (by omega)
          (by simpa using hrem2)
      refine ⟨reader', ?_, by rw [hbytes'], hrem'⟩
      rw [parseOneLengthAux]
      simp only [hr1, hr2, hadj, bind, Except.bind, if_true]
      exact hpar
termination_by (current - target) + (target - current)
decreasing_by all_goals omega

/-! ### Full code-length table -/

/-- Bits emitted for the per-symbol deltas of a table starting at `current`:
each symbol is `deltaBits ++ [false]`. -/
def tableBits : Nat → List Nat → List Bool
  | _, [] => []
  | current, target :: rest => deltaBits current target ++ false :: tableBits target rest

/-- `writeCodeLengthTableAux` emits exactly `tableBits`. -/
theorem writeCodeLengthTableAux_bits (lengths : List Nat) :
    ∀ (current : Nat) (w : BitWriter), w.WF →
      (writeCodeLengthTableAux current lengths w).bits = w.bits ++ tableBits current lengths
      ∧ (writeCodeLengthTableAux current lengths w).WF := by
  induction lengths with
  | nil => intro current w hw; refine ⟨by simp [writeCodeLengthTableAux, tableBits], hw⟩
  | cons target rest ih =>
      intro current w hw
      obtain ⟨hd, hdwf⟩ := writeLengthDelta_bits w hw current target
      have hbitwf : ((writeLengthDelta w current target).writeBit false).WF :=
        (writeLengthDelta w current target).writeBit_WF hdwf false
      obtain ⟨hrest, hrestwf⟩ :=
        ih target ((writeLengthDelta w current target).writeBit false) hbitwf
      refine ⟨?_, hrestwf⟩
      rw [writeCodeLengthTableAux, tableBits, hrest,
        (writeLengthDelta w current target).writeBit_bits hdwf false, hd]
      simp [List.append_assoc]

/-- `parseTableCodeLengthsAux` walks back exactly `tableBits`. -/
theorem parseTableCodeLengthsAux_of_prefix (lengths : List Nat) :
    ∀ (current : Nat) (acc : List Nat) (reader : BitReader) (rest : List Bool),
      current ≤ 20 → (∀ l ∈ lengths, l ≤ 20) →
      (bitListOf reader.bytes).drop reader.bitPos = tableBits current lengths ++ rest →
      ∃ reader', parseTableCodeLengthsAux lengths.length current reader acc
          = .ok (acc.reverse ++ lengths, reader')
        ∧ reader'.bytes = reader.bytes
        ∧ (bitListOf reader'.bytes).drop reader'.bitPos = rest := by
  induction lengths with
  | nil =>
      intro current acc reader rest _ _ hpre
      refine ⟨reader, ?_, rfl, by simpa [tableBits] using hpre⟩
      simp only [List.length_nil, parseTableCodeLengthsAux, List.append_nil]
      rfl
  | cons target rest ih =>
      intro current acc reader restBits hcur hvalid hpre
      have htarget : target ≤ 20 := hvalid target (by simp)
      rw [tableBits, List.append_assoc, List.cons_append] at hpre
      obtain ⟨reader1, hpar1, hbytes1, hrem1⟩ :=
        parseOneLengthAux_of_prefix current target htarget hcur
          (tableBits target rest ++ restBits) 64 reader (by omega) hpre
      obtain ⟨reader', hpar2, hbytes2, hrem2⟩ :=
        ih target (target :: acc) reader1 restBits htarget
          (fun l hl => hvalid l (by simp [hl])) hrem1
      refine ⟨reader', ?_, by rw [hbytes2, hbytes1], hrem2⟩
      rw [List.length_cons, parseTableCodeLengthsAux]
      simp only [hpar1, bind, Except.bind]
      rw [hpar2]
      simp

/-- Bits of a full code-length table: 5-bit start length then the per-symbol
deltas. -/
def codeLengthTableBits (lengths : List Nat) : List Bool :=
  natBitsMSB 5 (lengths.headD 0) ++ tableBits (lengths.headD 0) lengths

/-- **`writeCodeLengthTable` emits exactly `codeLengthTableBits`.** -/
theorem writeCodeLengthTable_bits (w : BitWriter) (hw : w.WF) (lengths : List Nat) :
    (writeCodeLengthTable w lengths).bits = w.bits ++ codeLengthTableBits lengths := by
  rw [writeCodeLengthTable, codeLengthTableBits]
  obtain ⟨hbits, _⟩ :=
    writeCodeLengthTableAux_bits lengths (lengths.headD 0) (w.writeBits 5 (lengths.headD 0))
      (w.writeBits_WF hw 5 (lengths.headD 0))
  rw [hbits, w.writeBits_bits hw 5 (lengths.headD 0), List.append_assoc]

/-- **Code-length table roundtrip.** A parser whose cursor begins with a written
table's bits recovers the lengths, given every length is in `[0, 20]`. -/
theorem parseTableCodeLengths_of_prefix (lengths : List Nat) (reader : BitReader) (rest : List Bool)
    (hvalid : ∀ l ∈ lengths, l ≤ 20)
    (hpre : (bitListOf reader.bytes).drop reader.bitPos = codeLengthTableBits lengths ++ rest) :
    ∃ reader', parseTableCodeLengths lengths.length reader = .ok (lengths, reader')
      ∧ reader'.bytes = reader.bytes
      ∧ (bitListOf reader'.bytes).drop reader'.bitPos = rest := by
  have hstart : lengths.headD 0 ≤ 20 := by
    cases lengths with
    | nil => simp
    | cons a as => exact hvalid a (by simp)
  rw [codeLengthTableBits, List.append_assoc] at hpre
  obtain ⟨hr5, hrem5⟩ :=
    readBits_of_prefix reader 5 (lengths.headD 0) (tableBits (lengths.headD 0) lengths ++ rest)
      (by omega) hpre
  obtain ⟨reader', hpar, hbytes, hrem⟩ :=
    parseTableCodeLengthsAux_of_prefix lengths (lengths.headD 0) []
      { reader with bitPos := reader.bitPos + 5 } rest hstart hvalid (by simpa using hrem5)
  refine ⟨reader', ?_, by rw [hbytes], hrem⟩
  rw [parseTableCodeLengths]
  simp only [hr5, bind, Except.bind, gt_iff_lt, pure, Except.pure,
    if_neg (by omega : ¬ 20 < lengths.headD 0)]
  exact hpar

end Bzip2.Format.BZ2
