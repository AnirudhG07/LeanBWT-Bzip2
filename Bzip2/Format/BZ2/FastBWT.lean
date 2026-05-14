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

private def rotationPairLE (ranks : Array Nat) (n step i j : Nat) : Bool :=
  let left := pairKey ranks n step i
  let right := pairKey ranks n step j
  if left.1 < right.1 then
    true
  else if right.1 < left.1 then
    false
  else if left.2 < right.2 then
    true
  else if right.2 < left.2 then
    false
  else
    decide (i ≤ j)

private def initialRanks (input : ByteArray) : Array Nat :=
  Array.ofFn (fun i : Fin input.size => input[i.1]!.toNat)

private def buildNextRanks
    (ranks : Array Nat) (n step : Nat) (order : List Nat) :
    Array Nat × Nat :=
  Id.run do
    let mut nextRanks := Array.replicate n 0
    match order with
    | [] => pure (nextRanks, 0)
    | first :: rest =>
        nextRanks := nextRanks.set! first 0
        let mut distinctRanks := 1
        let mut previousKey := pairKey ranks n step first
        for idx in rest do
          let key := pairKey ranks n step idx
          if key ≠ previousKey then
            distinctRanks := distinctRanks + 1
            previousKey := key
          nextRanks := nextRanks.set! idx (distinctRanks - 1)
        pure (nextRanks, distinctRanks)

private def sortedRotationIndices (input : ByteArray) : List Nat :=
  let n := input.size
  if n = 0 then
    []
  else
    Id.run do
      let mut order := List.range n
      let mut ranks := initialRanks input
      let mut step := 1
      while step < n do
        order := order.mergeSort (rotationPairLE ranks n step)
        let (nextRanks, distinctRanks) := buildNextRanks ranks n step order
        ranks := nextRanks
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
      Bzip2.Format.byteArrayOfList <|
        order.map (fun start => input[((start + n - 1) % n)]!)
    { lastColumn := lastColumn, origPtr := order.findIdx (· = 0) }

end Bzip2.Format.BZ2
