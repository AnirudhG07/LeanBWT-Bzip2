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
  · simp [h, beq_iff_eq]

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
      rw [hk]
      simp only [runaRunbBody, List.reverse_append, zeroRunCodeRev, List.reverse_reverse,
        List.append_assoc, List.cons_append, List.nil_append]
  | case3 alphabet bytes index zeroCount accRev h =>
      -- out of range: flush remaining pending zeros
      rw [encodeMtfAux, dif_neg h]
      have hdrop : bytes.toList.drop index = [] := by
        apply List.drop_eq_nil_of_le
        rw [toList_eq]; simpa using Nat.le_of_not_lt h
      rw [hdrop]
      simp only [mtfEncode, runaRunbBody, zeroRunCodeRev, List.reverse_append,
        List.reverse_reverse]
