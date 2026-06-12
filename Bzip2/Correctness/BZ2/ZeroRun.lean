import Bzip2.Format.BZ2.Transform

/-!
# RUNA/RUNB zero-run roundtrip

The exact `.bz2` MTF stream encodes runs of the zero MTF index in bijective
base 2 using the RUNA (`0`) and RUNB (`1`) symbols. This module models the
decoder's accumulation as `decodeZeroRun` and proves it inverts the encoder's
`zeroRunDigits`, discharging TODO Phase 5.2's RUNA/RUNB round trip at the
digit level.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

/-- Weight of one RUNA/RUNB digit: RUNA (`0`) = 1, RUNB (anything else) = 2. -/
def zeroDigitWeight (d : Nat) : Nat := if d = 0 then 1 else 2

/-- Value of a least-significant-first digit list: `Σ weight(dᵢ) · 2ⁱ`. -/
def evalZeroDigits : List Nat → Nat
  | [] => 0
  | d :: ds => zeroDigitWeight d + 2 * evalZeroDigits ds

/--
The decoder's running accumulation for RUNA/RUNB, matching the
`repeatCount`/`repeatPower` update in `decodeLastColumnLoop`. `rc` is the
accumulated count, `rp` the weight of the next digit; on the first digit
(`rc = 0`) the weight is reset to 1.
-/
def decodeZeroRunFrom (rc rp : Nat) : List Nat → Nat
  | [] => rc
  | d :: ds =>
      let rp' := if rc = 0 then 1 else rp
      decodeZeroRunFrom (rc + rp' * zeroDigitWeight d) (rp' * 2) ds

/-- Decode a full RUNA/RUNB digit stream (stream order = least significant first). -/
def decodeZeroRun (ds : List Nat) : Nat := decodeZeroRunFrom 0 0 ds

/-- Once the count is positive, the weight `rp` is never reset and the fold is linear. -/
theorem decodeZeroRunFrom_pos (ds : List Nat) (rc rp : Nat) (h : 0 < rc) :
    decodeZeroRunFrom rc rp ds = rc + evalZeroDigits ds * rp := by
  induction ds generalizing rc rp with
  | nil => simp [decodeZeroRunFrom, evalZeroDigits]
  | cons d ds ih =>
      have hrc : rc ≠ 0 := by omega
      have hw : 0 < zeroDigitWeight d := by unfold zeroDigitWeight; split <;> omega
      rw [decodeZeroRunFrom]
      simp only [hrc, if_false]
      rw [ih (rc + rp * zeroDigitWeight d) (rp * 2) (by omega)]
      simp only [evalZeroDigits]
      ring

/-- The bijective base-2 digits evaluate back to the original count. -/
theorem evalZeroDigits_zeroRunDigits (n : Nat) :
    evalZeroDigits (zeroRunDigits n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => simp [zeroRunDigits, evalZeroDigits]
      | count + 1 =>
          rw [zeroRunDigits, evalZeroDigits, ih (count / 2) (by omega)]
          unfold zeroDigitWeight
          split <;> omega

/-- Decoding a nonempty digit stream peels the first digit at weight 1. -/
theorem decodeZeroRun_cons (d : Nat) (ds : List Nat) :
    decodeZeroRun (d :: ds) = decodeZeroRunFrom (zeroDigitWeight d) 2 ds := by
  unfold decodeZeroRun
  simp [decodeZeroRunFrom]

/-- **RUNA/RUNB roundtrip:** decoding the encoded zero-run digits recovers the count. -/
theorem decodeZeroRun_zeroRunDigits (n : Nat) :
    decodeZeroRun (zeroRunDigits n) = n := by
  match n with
  | 0 => simp [decodeZeroRun, zeroRunDigits, decodeZeroRunFrom]
  | count + 1 =>
      have hpos : 0 < zeroDigitWeight (count % 2) := by
        unfold zeroDigitWeight; split <;> omega
      rw [zeroRunDigits, decodeZeroRun_cons,
        decodeZeroRunFrom_pos _ _ _ hpos, evalZeroDigits_zeroRunDigits]
      unfold zeroDigitWeight
      split <;> omega

end Bzip2.Format.BZ2
