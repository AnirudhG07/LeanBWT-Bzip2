import Bzip2.Format.BZ2.Encoder
import Bzip2.Format.BZ2.Parser
import Mathlib

/-!
# Selector move-to-front roundtrip

Each Huffman-table selector is encoded as its position in a move-to-front list
initialised to `List.range groupCount`; the parser maps positions back to values
with the identical move-to-front update. This module proves the transform
round-trips: decoding the encoded selector indices recovers the selectors,
whenever every selector is a valid group index.

The decoder model `decodeSelectorsAux` mirrors `Parser.parseSelectorsAux`'s
move-to-front fold (`moveToFrontIndex`), without the unary bit reading — that bit
layer is handled separately by `BitsReader`.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

/-- Pure model of the parser's selector move-to-front decode, over an index
list (post unary-decode). -/
def decodeSelectorsAux : List Nat → List Nat → List Nat → Except String (List Nat)
  | [], _, acc => .ok acc.reverse
  | index :: rest, mtf, acc => do
      let (value, mtf') ← moveToFrontIndex index mtf
      decodeSelectorsAux rest mtf' (value :: acc)

/-- Decode a full selector-index list against the initial `range groupCount` MTF. -/
def decodeSelectors (groupCount : Nat) (indices : List Nat) : Except String (List Nat) :=
  decodeSelectorsAux indices (List.range groupCount) []

/-- A present value is found by `findIdx (· = value)` and reads back at that index. -/
theorem mtf_findIdx_getElem? (s : Nat) (mtf : List Nat) (h : s ∈ mtf) :
    mtf[mtf.findIdx (· = s)]? = some s := by
  have hlt : mtf.findIdx (· = s) < mtf.length :=
    List.findIdx_lt_length_of_exists ⟨s, h, by simp⟩
  rw [List.getElem?_eq_getElem hlt]
  congr 1
  have hp : (mtf[mtf.findIdx (· = s)]'hlt = s) := by
    have := List.findIdx_getElem (p := (· = s)) (xs := mtf) (w := hlt)
    simpa using this
  exact hp

/-- Move-to-front preserves the underlying set, so membership of the remaining
selectors is preserved. -/
theorem mem_moveToFront {x s : Nat} {mtf : List Nat} (hx : x ∈ mtf) :
    x ∈ s :: mtf.erase s := by
  by_cases hxs : x = s
  · simp [hxs]
  · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne hxs).mpr hx)

/-- Move-to-front preserves nodup. -/
theorem nodup_moveToFront {s : Nat} {mtf : List Nat} (h : mtf.Nodup) :
    (s :: mtf.erase s).Nodup := by
  refine List.nodup_cons.mpr ⟨?_, h.erase s⟩
  exact h.not_mem_erase

/-- **Joint roundtrip on the move-to-front aux.** Encoding the selectors against a
nodup MTF that contains them succeeds, and decoding the produced indices recovers
the selectors. -/
theorem roundtrip_aux (selectors mtf accE : List Nat)
    (hnodup : mtf.Nodup) (hmem : ∀ s ∈ selectors, s ∈ mtf) :
    ∃ idxs, encodeSelectorsAux selectors mtf accE = .ok (accE.reverse ++ idxs) ∧
      ∀ accD, decodeSelectorsAux idxs mtf accD = .ok (accD.reverse ++ selectors) := by
  induction selectors generalizing mtf accE with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp only [encodeSelectorsAux, List.append_nil]; rfl
      · intro accD; simp [decodeSelectorsAux]
  | cons s rest ih =>
      have hs : s ∈ mtf := hmem s (by simp)
      -- encode this step
      have henc : moveToFrontValue s mtf = .ok (mtf.findIdx (· = s), s :: mtf.erase s) := by
        simp only [moveToFrontValue, mtf_findIdx_getElem? s mtf hs]; rfl
      have hdi : moveToFrontIndex (mtf.findIdx (· = s)) mtf = .ok (s, s :: mtf.erase s) := by
        simp only [moveToFrontIndex, mtf_findIdx_getElem? s mtf hs]
      -- recurse on the updated MTF
      have hnodup' : (s :: mtf.erase s).Nodup := nodup_moveToFront hnodup
      have hmem' : ∀ x ∈ rest, x ∈ s :: mtf.erase s := by
        intro x hx; exact mem_moveToFront (hmem x (by simp [hx]))
      obtain ⟨idxs', henc', hdec'⟩ :=
        ih (s :: mtf.erase s) (mtf.findIdx (· = s) :: accE) hnodup' hmem'
      refine ⟨mtf.findIdx (· = s) :: idxs', ?_, ?_⟩
      · -- encode result
        simp only [encodeSelectorsAux, henc, bind, Except.bind, henc']
        simp [List.reverse_cons]
      · -- decode result
        intro accD
        simp only [decodeSelectorsAux, hdi, bind, Except.bind]
        rw [hdec' (s :: accD)]
        simp [List.reverse_cons]

/-- **Selector MTF roundtrip.** Decoding the encoded selector indices recovers the
original selectors, when every selector is a valid Huffman-group index. -/
theorem decodeSelectors_encodeSelectors (groupCount : Nat) (selectors : List Nat)
    (hvalid : ∀ s ∈ selectors, s < groupCount) :
    ∀ idxs, encodeSelectors groupCount selectors = .ok idxs →
      decodeSelectors groupCount idxs = .ok selectors := by
  have hmem : ∀ s ∈ selectors, s ∈ List.range groupCount := by
    intro s hs; exact List.mem_range.mpr (hvalid s hs)
  obtain ⟨idxs, henc, hdec⟩ :=
    roundtrip_aux selectors (List.range groupCount) [] (List.nodup_range) hmem
  intro idxs' henc'
  rw [encodeSelectors, henc] at henc'
  simp only [List.reverse_nil, List.nil_append, Except.ok.injEq] at henc'
  subst henc'
  rw [decodeSelectors, hdec []]
  simp

end Bzip2.Format.BZ2
