import Bzip2.Format.BZ2.Transform
import Bzip2.Correctness.BZ2.ZeroRun
import Bzip2.Correctness.BZ2.RLE1
import Bzip2.Correctness.MTF
import Bzip2.BWT

/-!
# MTF + RUNA/RUNB payload roundtrip

The exact `.bz2` block payload is the BWT last column run through move-to-front,
then a bijective base-2 (RUNA/RUNB) coding of runs of the zero MTF index, with a
trailing end-of-block symbol. This module proves the payload round-trips at the
symbol-list level: a pure decoder model recovers the last column from the symbol
stream the encoder emits.

The argument factors cleanly:
* a structural forward model `runaRunbBody` of the encoder body, proved equal to
  the runtime index-based `encodeMtfAux`;
* a pure decoder model `decodeMtfRun` mirroring `decodeLastColumnLoop`'s
  `repeatCount`/`repeatPower` accumulation and MTF stepping;
* the round trip, reusing `decodeZeroRun_zeroRunDigits` (RUNA/RUNB) and
  `Bzip2.mtfDecode_mtfEncode_of_nodup` (move-to-front).
-/

namespace Bzip2.Format.BZ2

open Bzip2 (mtfEncode mtfDecode)

set_option autoImplicit false

/-! ### Encoder body model -/

/-- Structural forward model of the RUNA/RUNB body: `z` zeros are pending; a
nonzero MTF index `n+1` flushes the pending zeros (as `zeroRunDigits z`, least
significant first) and emits `n+2`. -/
def runaRunbBody : Nat → List Nat → List Nat
  | z, [] => zeroRunDigits z
  | z, 0 :: is => runaRunbBody (z + 1) is
  | z, (n + 1) :: is => zeroRunDigits z ++ (n + 2) :: runaRunbBody 0 is

/-- The encoder's `decide (· = byte)` and move-to-front's `· == byte` predicates
agree on bytes. -/
theorem decide_eq_beq_fun (byte : UInt8) :
    (fun x : UInt8 => decide (x = byte)) = (fun x : UInt8 => x == byte) := by
  funext x
  by_cases h : x = byte
  · simp [h]
  · simp [h]

/-- Unfold one move-to-front step. -/
theorem mtfEncode_cons (alphabet : List UInt8) (x : UInt8) (xs : List UInt8) :
    mtfEncode alphabet (x :: xs)
      = alphabet.findIdx (· == x) :: mtfEncode (x :: alphabet.erase x) xs := rfl

/-- One element of `bytes.toList.drop index` when `index` is in range. -/
theorem drop_index_eq (bytes : ByteArray) (index : Nat) (h : index < bytes.size) :
    bytes.toList.drop index = bytes[index] :: bytes.toList.drop (index + 1) := by
  have hi : index < bytes.data.toList.length := by simpa using h
  rw [toList_eq, List.drop_eq_getElem_cons hi]
  congr 1

/-- **The runtime encoder body equals the structural model.** Reversing the
index-based `encodeMtfAux` accumulator yields the prefix `accRev.reverse` followed
by `runaRunbBody` applied to the move-to-front indices of the remaining bytes. -/
theorem encodeMtfAux_reverse (alphabet : List UInt8) (bytes : ByteArray)
    (index zeroCount : Nat) (accRev : List Nat) :
    (encodeMtfAux alphabet bytes index zeroCount accRev).reverse
      = accRev.reverse ++ runaRunbBody zeroCount (mtfEncode alphabet (bytes.toList.drop index)) := by
  induction alphabet, bytes, index, zeroCount, accRev using encodeMtfAux.induct with
  | case1 alphabet bytes index zeroCount accRev h byte mtfIndex alphabet' hz ih =>
      -- in range, MTF index 0: accumulate a pending zero
      rw [encodeMtfAux, dif_pos h, if_pos hz, ih,
        drop_index_eq bytes index h, mtfEncode_cons, ← decide_eq_beq_fun]
      rw [show List.findIdx (fun x => decide (x = bytes[index])) alphabet = 0 from hz]
      rfl
  | case2 alphabet bytes index zeroCount accRev h byte mtfIndex alphabet' hz accRev1 ih =>
      -- in range, nonzero MTF index: flush pending zeros and emit `index+1`
      rw [encodeMtfAux, dif_pos h, if_neg hz, ih,
        drop_index_eq bytes index h, mtfEncode_cons, ← decide_eq_beq_fun]
      obtain ⟨k, hk⟩ : ∃ k, List.findIdx (fun x => decide (x = bytes[index])) alphabet = k + 1 :=
        Nat.exists_eq_succ_of_ne_zero hz
      simp +zetaDelta only [hk, zeroRunCodeRev, List.reverse_cons, List.reverse_append,
        List.reverse_reverse, List.append_assoc, List.cons_append, List.nil_append, runaRunbBody]
  | case3 alphabet bytes index zeroCount accRev h =>
      -- out of range: flush remaining pending zeros
      rw [encodeMtfAux, dif_neg h]
      have hdrop : bytes.toList.drop index = [] := by
        apply List.drop_eq_nil_of_le
        rw [toList_eq]; simpa using Nat.le_of_not_lt h
      rw [hdrop]
      simp only [mtfEncode, runaRunbBody, zeroRunCodeRev, List.reverse_append,
        List.reverse_reverse]

/-- The full encoder body, characterised structurally: the move-to-front index
list of the last column, RUNA/RUNB-coded, followed by the end-of-block symbol. -/
theorem encodeMtfRunaRunb_eq (alphabet : List UInt8) (lc : ByteArray) :
    encodeMtfRunaRunb alphabet lc
      = runaRunbBody 0 (mtfEncode alphabet lc.toList) ++ [alphabet.length + 1] := by
  unfold encodeMtfRunaRunb
  rw [List.reverse_cons, encodeMtfAux_reverse]
  simp

/-! ### Decoder model -/

/-- Pure model of the post-Huffman MTF/RUNA/RUNB decoder, mirroring
`decodeLastColumnLoop`'s `repeatCount`/`repeatPower` accumulation and MTF
stepping. Structural on the symbol list. `outRev` is the reversed output so far;
on a symbol `< 2` the zero-run count `rc` accumulates (weight `rp`), and on a
symbol `≥ 2` the pending zeros flush as copies of the MTF front before the
end-of-block check or the next MTF byte. -/
def decodeMtfBody (eob : Nat) :
    List UInt8 → Nat → Nat → List UInt8 → List Nat → Option (List UInt8)
  | _, _, _, _, [] => none
  | alphabet, rc, rp, outRev, s :: ss =>
      if s < 2 then
        let rp' := if rc = 0 then 1 else rp
        decodeMtfBody eob alphabet (rc + rp' * (if s = 0 then 1 else 2)) (rp' * 2) outRev ss
      else
        let h := alphabet.headD default
        let outRev' := List.replicate rc h ++ outRev
        if s = eob then some outRev'.reverse
        else
          let byte := alphabet[s - 1]!
          decodeMtfBody eob (byte :: alphabet.erase byte) 0 0 (byte :: outRev') ss

/-- RUNA/RUNB digits are all `0` or `1`. -/
theorem zeroRunDigits_lt_two (n : Nat) : ∀ d ∈ zeroRunDigits n, d < 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => simp [zeroRunDigits]
      | m + 1 =>
          rw [zeroRunDigits]
          intro d hd
          rw [List.mem_cons] at hd
          rcases hd with hd | hd
          · omega
          · exact ih (m / 2) (by omega) d hd

/-- On a symbol `≥ 2` the decoder ignores the `repeatPower` slot. -/
theorem decodeMtfBody_rp_irrel (eob : Nat) (alphabet : List UInt8) (rc rp1 rp2 : Nat)
    (outRev : List UInt8) (s : Nat) (ss : List Nat) (hs : 2 ≤ s) :
    decodeMtfBody eob alphabet rc rp1 outRev (s :: ss)
      = decodeMtfBody eob alphabet rc rp2 outRev (s :: ss) := by
  rw [decodeMtfBody, decodeMtfBody, if_neg (Nat.not_lt.mpr hs), if_neg (Nat.not_lt.mpr hs)]

/-- Consuming a block of RUNA/RUNB digits accumulates the zero count (via
`decodeZeroRunFrom`); the following symbol is `≥ 2`, so the `repeatPower` slot
left dangling is irrelevant. -/
theorem decode_zero_block (eob : Nat) (alphabet : List UInt8) (outRev : List UInt8)
    (s : Nat) (ss : List Nat) (hs : 2 ≤ s) :
    ∀ (ds : List Nat), (∀ d ∈ ds, d < 2) → ∀ rc rp,
      decodeMtfBody eob alphabet rc rp outRev (ds ++ s :: ss)
        = decodeMtfBody eob alphabet (decodeZeroRunFrom rc rp ds) rp outRev (s :: ss) := by
  intro ds
  induction ds with
  | nil => intro _ rc rp; simp [decodeZeroRunFrom]
  | cons d ds ih =>
      intro hds rc rp
      have hd2 : d < 2 := hds d (by simp)
      have hdtail : ∀ d' ∈ ds, d' < 2 := fun d' hd' => hds d' (by simp [hd'])
      rw [List.cons_append, decodeMtfBody, if_pos (by omega),
        ih hdtail (rc + (if rc = 0 then 1 else rp) * (if d = 0 then 1 else 2))
          ((if rc = 0 then 1 else rp) * 2)]
      rw [show decodeZeroRunFrom rc rp (d :: ds)
            = decodeZeroRunFrom (rc + (if rc = 0 then 1 else rp) * zeroDigitWeight d)
                ((if rc = 0 then 1 else rp) * 2) ds from rfl]
      exact decodeMtfBody_rp_irrel eob alphabet _ _ rp outRev s ss hs

/-- Decoding `z` leading zero MTF indices emits `z` copies of the alphabet head
and leaves the alphabet unchanged. -/
theorem mtfDecode_replicate_zero (a : UInt8) (t : List UInt8) (z : Nat) (rest : List Nat) :
    mtfDecode (a :: t) (List.replicate z 0 ++ rest)
      = List.replicate z a ++ mtfDecode (a :: t) rest := by
  induction z with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append, mtfDecode]
      have h0 : (a :: t)[0]! = a := by simp
      rw [h0, List.erase_cons_head, ih, List.replicate_succ, List.cons_append]

/-- **Decoder model inverts the encoder body.** Reading `runaRunbBody z is`
followed by the end-of-block symbol reproduces the move-to-front decoding of the
index list (with `z` pending zero indices), appended to the reversed output. -/
theorem decode_runaRunbBody (eob : Nat) :
    ∀ (is : List Nat) (alphabet : List UInt8) (z : Nat) (outRev : List UInt8),
      alphabet ≠ [] → eob = alphabet.length + 1 → (∀ i ∈ is, i < alphabet.length) →
      decodeMtfBody eob alphabet 0 0 outRev (runaRunbBody z is ++ [eob])
        = some (outRev.reverse ++ mtfDecode alphabet (List.replicate z 0 ++ is)) := by
  intro is
  induction is with
  | nil =>
      intro alphabet z outRev hne heob _
      obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
      have heob2 : 2 ≤ eob := by rw [heob]; simp
      have hz0 : decodeZeroRunFrom 0 0 (zeroRunDigits z) = z := decodeZeroRun_zeroRunDigits z
      rw [runaRunbBody,
        decode_zero_block eob (a :: t) outRev eob [] heob2 (zeroRunDigits z)
          (zeroRunDigits_lt_two z) 0 0, hz0,
        decodeMtfBody, if_neg (by omega : ¬ eob < 2), if_pos rfl,
        mtfDecode_replicate_zero]
      simp [mtfDecode, List.reverse_append, List.reverse_replicate]
  | cons i is ih =>
      intro alphabet z outRev hne heob hlt
      match i with
      | 0 =>
          -- zero index: fold into the pending run
          rw [runaRunbBody]
          rw [ih alphabet (z + 1) outRev hne heob (fun j hj => hlt j (by simp [hj]))]
          congr 2
          rw [List.replicate_succ']
          simp
      | n + 1 =>
          obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
          have heob2 : 2 ≤ eob := by rw [heob]; simp
          have hlt1 : n + 1 < (a :: t).length := hlt (n + 1) (by simp)
          have hne_eob : ¬ (n + 2 = eob) := by rw [heob]; omega
          have hge2 : 2 ≤ n + 2 := by omega
          have hz0 : decodeZeroRunFrom 0 0 (zeroRunDigits z) = z := decodeZeroRun_zeroRunDigits z
          have hbyte_mem : (a :: t)[n + 1]! ∈ (a :: t) := by
            rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt1]
            exact List.getElem_mem hlt1
          have hlen' : ((a :: t)[n + 1]! :: (a :: t).erase (a :: t)[n + 1]!).length
              = (a :: t).length := by
            rw [List.length_cons, List.length_erase_of_mem hbyte_mem]
            simp
          have hbyte : (n + 2) - 1 = n + 1 := by omega
          rw [runaRunbBody, List.append_assoc, List.cons_append,
            decode_zero_block eob (a :: t) outRev (n + 2) (runaRunbBody 0 is ++ [eob]) hge2
              (zeroRunDigits z) (zeroRunDigits_lt_two z) 0 0, hz0,
            decodeMtfBody, if_neg (by omega : ¬ n + 2 < 2), if_neg hne_eob, hbyte]
          -- recurse with the updated alphabet
          rw [ih ((a :: t)[n + 1]! :: (a :: t).erase (a :: t)[n + 1]!) 0
            ((a :: t)[n + 1]! :: (List.replicate z ((a :: t).headD default) ++ outRev))
            (by simp) (by rw [hlen']; exact heob)
            (fun j hj => by rw [hlen']; exact hlt j (by simp [hj]))]
          -- both sides: assemble the byte and pending zeros into the mtfDecode
          rw [mtfDecode_replicate_zero a t z ((n + 1) :: is), mtfDecode]
          simp only [List.headD_cons, List.replicate_zero, List.nil_append,
            List.reverse_cons, List.reverse_append, List.reverse_replicate,
            List.append_assoc, List.cons_append, List.nil_append]

/-- Every move-to-front index is a valid alphabet position when the alphabet
covers the message. -/
theorem mtfEncode_lt_length (alphabet : List UInt8) (xs : List UInt8)
    (h : ∀ x ∈ xs, x ∈ alphabet) : ∀ i ∈ mtfEncode alphabet xs, i < alphabet.length := by
  induction xs generalizing alphabet with
  | nil => simp [mtfEncode]
  | cons x xs ih =>
      intro i hi
      have hx : x ∈ alphabet := h x (by simp)
      rw [mtfEncode_cons, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact List.findIdx_lt_length_of_exists ⟨x, hx, by simp⟩
      · have hsub : ∀ y ∈ xs, y ∈ (x :: alphabet.erase x) := by
          intro y hy
          have hya : y ∈ alphabet := h y (by simp [hy])
          by_cases hyx : y = x
          · simp [hyx]
          · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne hyx).mpr hya)
        have hrec := ih (x :: alphabet.erase x) hsub i hi
        rwa [List.length_cons, List.length_erase_of_mem hx,
          Nat.sub_add_cancel (by simp [Nat.one_le_iff_ne_zero, List.length_eq_zero_iff,
            List.ne_nil_of_mem hx])] at hrec

/-- **MTF + RUNA/RUNB roundtrip.** The decoder model recovers the BWT last column
from the encoder's symbol stream, given a nodup alphabet covering its bytes. -/
theorem decodeMtfBody_encodeMtfRunaRunb (alphabet : List UInt8) (lc : ByteArray)
    (hne : alphabet ≠ []) (hnodup : alphabet.Nodup)
    (hcov : ∀ x ∈ lc.toList, x ∈ alphabet) :
    decodeMtfBody (alphabet.length + 1) alphabet 0 0 [] (encodeMtfRunaRunb alphabet lc)
      = some lc.toList := by
  rw [encodeMtfRunaRunb_eq]
  have hlt : ∀ i ∈ mtfEncode alphabet lc.toList, i < alphabet.length :=
    mtfEncode_lt_length alphabet lc.toList hcov
  rw [decode_runaRunbBody (alphabet.length + 1) (mtfEncode alphabet lc.toList) alphabet 0 []
    hne rfl hlt]
  rw [List.replicate_zero, List.nil_append, List.reverse_nil, List.nil_append,
    Bzip2.mtfDecode_mtfEncode_of_nodup alphabet lc.toList hnodup hcov]
