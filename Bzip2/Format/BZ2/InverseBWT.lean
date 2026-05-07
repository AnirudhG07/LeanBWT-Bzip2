import Bzip2.Format.Bytes
import Mathlib

/-!
Standard `origPtr`-based inverse BWT for exact `.bz2` blocks.

This is separate from the project's sentinel-based semantic specification
because the real `.bz2` wire format uses the conventional primary-index style
Burrows-Wheeler transform.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

private def countByte (counts : Array Nat) (byte : UInt8) : Array Nat :=
  let idx := byte.toNat
  counts.set! idx (counts[idx]! + 1)

private def byteCounts (last : ByteArray) : Array Nat :=
  last.foldl countByte (Array.replicate 256 0)

private def prefixStarts (counts : Array Nat) : Array Nat :=
  Id.run do
    let mut starts := Array.replicate 256 0
    let mut sum := 0
    for i in [0:256] do
      starts := starts.set! i sum
      sum := sum + counts[i]!
    pure starts

private def buildTransitionTable (last : ByteArray) (starts : Array Nat) : Array Nat :=
  Id.run do
    let mut next := starts
    let mut table := Array.ofFn (fun i : Fin last.size => last[i.1]!.toNat)
    for i in [0:last.size] do
      let byte := last[i]!
      let bucket := byte.toNat
      let pos := next[bucket]!
      table := table.set! pos (table[pos]! + i * 256)
      next := next.set! bucket (pos + 1)
    pure table

private def recoverBytes (table : Array Nat) (origPtr size : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.empty
    let mut pos := table[origPtr]! / 256
    for _ in [0:size] do
      let entry := table[pos]!
      out := out.push (UInt8.ofNat entry)
      pos := entry / 256
    pure out

/-- Invert the standard `origPtr`-based BWT used by exact `.bz2` blocks. -/
def inverseBWT (last : ByteArray) (origPtr : Nat) : Except String ByteArray := do
  if last.size = 0 then
    if origPtr = 0 then
      pure ByteArray.empty
    else
      throw "Exact `.bz2` block has an invalid primary index for an empty BWT column."
  else if origPtr ≥ last.size then
    throw "Exact `.bz2` block primary index is outside the BWT column."
  else
    let counts := byteCounts last
    let starts := prefixStarts counts
    let table := buildTransitionTable last starts
    pure (recoverBytes table origPtr last.size)

end Bzip2.Format.BZ2
