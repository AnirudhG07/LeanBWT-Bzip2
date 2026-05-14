import Bzip2.Format.Bytes
import Mathlib

/-!
Practical forward BWT for exact `.bz2` blocks.

This module is intentionally separate from the project's original proved BWT
construction. It implements a runtime-oriented cyclic-rotation sorter over index
ranks rather than materializing and comparing whole rotations directly.

The original proved BWT remains the semantic reference; this module is the
execution-oriented forward transform used by the exact `.bz2` encoder.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

/-- Runtime BWT result for one exact `.bz2` block. -/
structure FastBWTResult where
  lastColumn : ByteArray
  origPtr : Nat
deriving DecidableEq

private def pairKey (ranks : Array Nat) (n step idx : Nat) : Nat × Nat :=
  let next := (idx + step) % n
  (ranks[idx]!, ranks[next]!)

private def initialRanks (input : ByteArray) : Array Nat :=
  Array.ofFn (fun i : Fin input.size => input[i.1]!.toNat)

private def countingSortBy
    (order : Array Nat)
    (keyBound : Nat)
    (key : Nat → Nat) :
    Array Nat :=
  Id.run do
    let mut counts := Array.replicate keyBound 0
    for idx in order do
      let bucket := key idx
      counts := counts.set! bucket (counts[bucket]! + 1)
    let mut starts := Array.replicate keyBound 0
    let mut offset := 0
    for bucket in [0:keyBound] do
      starts := starts.set! bucket offset
      offset := offset + counts[bucket]!
    let mut out := Array.replicate order.size 0
    for idx in order do
      let bucket := key idx
      let position := starts[bucket]!
      out := out.set! position idx
      starts := starts.set! bucket (position + 1)
    pure out

private def sortRotationPairs
    (ranks : Array Nat)
    (n step classCount : Nat)
    (order : Array Nat) :
    Array Nat :=
  let bySecond :=
    countingSortBy order classCount (fun idx => ranks[((idx + step) % n)]!)
  countingSortBy bySecond classCount (fun idx => ranks[idx]!)

private def buildNextRanks
    (ranks : Array Nat) (n step : Nat) (order : Array Nat) :
    Array Nat × Nat :=
  Id.run do
    let mut nextRanks := Array.replicate n 0
    if order.isEmpty then
      pure (nextRanks, 0)
    else
      let first := order[0]!
      nextRanks := nextRanks.set! first 0
      let mut distinctRanks := 1
      let mut previousKey := pairKey ranks n step first
      for i in [1:order.size] do
        let idx := order[i]!
        let key := pairKey ranks n step idx
        if key ≠ previousKey then
          distinctRanks := distinctRanks + 1
          previousKey := key
        nextRanks := nextRanks.set! idx (distinctRanks - 1)
      pure (nextRanks, distinctRanks)

private def sortedRotationIndices (input : ByteArray) : Array Nat :=
  let n := input.size
  if n = 0 then
    #[]
  else
    Id.run do
      let mut order := Array.range n
      let mut ranks := initialRanks input
      let mut classCount := 256
      let mut step := 1
      while step < n do
        order := sortRotationPairs ranks n step classCount order
        let (nextRanks, distinctRanks) := buildNextRanks ranks n step order
        ranks := nextRanks
        classCount := distinctRanks
        if distinctRanks = n then
          step := n
        else
          step := step * 2
      pure order

/-- Practical cyclic-rotation BWT for exact `.bz2` blocks. -/
def transformFastBWT (input : ByteArray) : FastBWTResult :=
  let n := input.size
  if n = 0 then
    { lastColumn := ByteArray.empty, origPtr := 0 }
  else
    let order := sortedRotationIndices input
    let lastColumn :=
      order.foldl
        (fun out start => out.push input[((start + n - 1) % n)]!)
        ByteArray.empty
    { lastColumn := lastColumn, origPtr := order.findIdx? (· = 0) |>.getD 0 }

end Bzip2.Format.BZ2
