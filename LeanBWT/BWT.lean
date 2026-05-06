import Mathlib

namespace LeanBWT

set_option autoImplicit false

variable {α : Type} [LinearOrder α] [DecidableEq α]

abbrev Symbol (α : Type) := WithBot α

instance symbolLinearOrder : LinearOrder (Symbol α) := inferInstance
instance symbolDecidableEq : DecidableEq (Symbol α) := inferInstance

/-- Append a unique minimal sentinel (`⊥`) to the end of the text. -/
def withSentinel (xs : List α) : List (Symbol α) :=
  xs.map (fun x => (x : Symbol α)) ++ [⊥]

/-- Lexicographic `≤` as a boolean comparator for merge sort. -/
def lexLE {β : Type} [LinearOrder β] : List β → List β → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if x < y then
        true
      else if y < x then
        false
      else
        lexLE xs ys

/-- Stable lexicographic sorting of rows. -/
def sortRows (rows : List (List (Symbol α))) : List (List (Symbol α)) :=
  rows.mergeSort lexLE

/-- Cyclic left rotation by `k` positions. -/
def rotateLeft {β : Type} (xs : List β) (k : Nat) : List β :=
  let n := xs.length
  let k' := k % n
  xs.drop k' ++ xs.take k'

/-- All cyclic rotations of the sentinel-augmented text. -/
@[simp, grind .]
def rotations (xs : List α) : List (List (Symbol α)) :=
  let ys := withSentinel xs
  (List.range ys.length).map (fun i => rotateLeft ys i)

/-- The sorted BWT matrix. -/
@[simp, grind .]
def bwtmatrix (xs : List α) : List (List (Symbol α)) :=
  sortRows (rotations xs)

/-- Last column of the BWT matrix. -/
@[simp, grind .]
def lastColumn (rows : List (List (Symbol α))) : List (Symbol α) :=
  rows.map (fun row => row.getLastD ⊥)

/-- Sort symbols to reconstruct the first column from the last column. -/
@[simp, grind .]
def firstColumn (last : List (Symbol α)) : List (Symbol α) :=
  last.mergeSort (fun a b => decide (a ≤ b))

/-- Number of occurrences of `c` in `xs[0:i)`. -/
def occBefore (xs : List (Symbol α)) (i : Nat) (c : Symbol α) : Nat :=
  (xs.take i).count c

/-- LF-step formula (index-level first/last correspondence helper). -/
@[simp, grind .]
def lfStep (last : List (Symbol α)) (i : Nat) : Nat :=
  let c := last.getD i ⊥
  let k := occBefore last i c
  let first := firstColumn last
  first.idxOfNth c k

/-- Structured BWT output. -/
structure BWTResult (α : Type) where
  original : List α
  last : List (Symbol α)
  primary : Nat
  deriving Repr

/-- Forward Burrows-Wheeler transform. -/
@[simp, grind .]
def transform (xs : List α) : BWTResult α :=
  let rows := bwtmatrix xs
  let s := withSentinel xs
  {
    original := xs
    last := lastColumn rows
    primary := rows.findIdx (fun row => decide (row = s))
  }

/-- Inverse Burrows-Wheeler transform API. -/
@[simp, grind .]
def lfCollect (last : List (Symbol α)) : Nat → Nat → List (Symbol α)
  | 0, _ => []
  | Nat.succ k, j =>
      let j' := lfStep last j
      last.getD j' ⊥ :: lfCollect last k j'

/-- Remove the unique sentinel from decoded symbols. -/
def stripSentinel (xs : List (Symbol α)) : List α :=
  xs.filterMap id

/-- Algorithmic inverse from `(last, primary)` using LF traversal. -/
@[simp, grind .]
def inverseFromLast (last : List (Symbol α)) (primary : Nat) : List α :=
  stripSentinel ((lfCollect last last.length primary).reverse)

/-- Algorithmic inverse on structured BWT payload. -/
def inverseAlgorithmic (r : BWTResult α) : List α :=
  inverseFromLast r.last r.primary

/-- Inverse Burrows-Wheeler transform API. -/
@[simp, grind .]
def inverse (r : BWTResult α) : List α :=
  inverseAlgorithmic r

/-- Run-length encoding helper. -/
def rleAux {β : Type} [DecidableEq β] (current : β) (count : Nat) : List β → List (β × Nat)
  | [] => [(current, count)]
  | y :: ys =>
      if y = current then
        rleAux current (count + 1) ys
      else
        (current, count) :: rleAux y 1 ys

/-- Run-length encoding. -/
def rleEncode {β : Type} [DecidableEq β] : List β → List (β × Nat)
  | [] => []
  | x :: xs => rleAux x 1 xs

/-- Run-length decoding. -/
def rleDecode {β : Type} : List (β × Nat) → List β
  | [] => []
  | (x, n) :: rest => List.replicate n x ++ rleDecode rest

/-- Compressed payload with BWT metadata plus RLE payload. -/
structure Compressed (α : Type) where
  bwt : BWTResult α
  payload : List (Symbol α × Nat)
  deriving Repr

/-- Compression: BWT then RLE on the BWT last column. -/
@[simp, grind .]
def compress (xs : List α) : Compressed α :=
  let b := transform xs
  { bwt := b, payload := rleEncode b.last }

/-- Decompression: decode payload, verify column, then inverse. -/
@[simp, grind .]
def decompress (c : Compressed α) : List α :=
  let decoded := rleDecode c.payload
  if decoded = c.bwt.last then
    inverse c.bwt
  else
    []

end LeanBWT
