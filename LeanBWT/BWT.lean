import Init.Data.List.Sort.Basic

namespace LeanBWT

variable {α : Type} [Ord α] [Inhabited α] [DecidableEq α]

/-- Lexicographic sorting of rows (lists) for the BWT matrix. -/
def sortRows (rows : List (List α)) : List (List α) :=
  rows.mergeSort (fun a b => compare a b != Ordering.gt)

/-- Cyclic left rotation by `k` positions. -/
def rotateLeft (xs : List α) (k : Nat) : List α :=
  let n := xs.length
  let k' := k % n
  xs.drop k' ++ xs.take k'

/-- All cyclic rotations of a list. For `[]`, we use `[[]]`. -/
def rotations (xs : List α) : List (List α) :=
  match xs with
  | [] => [[]]
  | _ => (List.range xs.length).map (fun i => rotateLeft xs i)

/-- The sorted BWT matrix. -/
def bwtmatrix (xs : List α) : List (List α) :=
  sortRows (rotations xs)

/-- Last column of the matrix. -/
def lastColumn (rows : List (List α)) : List α :=
  rows.map (fun row => row.getLastD default)

/-- Primary index (row index of original input in sorted matrix). -/
def primaryIndex (xs : List α) : Nat :=
  let rows := bwtmatrix xs
  rows.findIdx (fun row => decide (row = xs))

/-- Forward Burrows-Wheeler transform (last column + primary index). -/
def transform (xs : List α) : List α × Nat :=
  let rows := bwtmatrix xs
  (lastColumn rows, rows.findIdx (fun row => decide (row = xs)))

/-- One inverse-BWT refinement step: prefix with last-column symbols, then re-sort. -/
def inverseStep (last : List α) (table : List (List α)) : List (List α) :=
  let prefixed := List.zipWith (fun c row => c :: row) last table
  sortRows prefixed

/-- Iteratively reconstruct the table from the BWT last column. -/
def buildTable (last : List α) : Nat → List (List α)
  | 0 => List.replicate last.length []
  | n + 1 => inverseStep last (buildTable last n)

/-- Inverse Burrows-Wheeler transform. -/
def inverse (last : List α) (primary : Nat) : List α :=
  let table := buildTable last last.length
  table.getD primary []

/-- A simple run-length encoding. -/
def rleAux (current : α) (count : Nat) : List α → List (α × Nat)
  | [] => [(current, count)]
  | y :: ys =>
      if y = current then
        rleAux current (count + 1) ys
      else
        (current, count) :: rleAux y 1 ys

/-- A simple run-length encoding. -/
def rleEncode : List α → List (α × Nat)
  | [] => []
  | x :: xs => rleAux x 1 xs

/-- Decode run-length encoded data. -/
def rleDecode : List (α × Nat) → List α
  | [] => []
  | (x, n) :: rest => List.replicate n x ++ rleDecode rest

/-- BWT payload suitable for later entropy coding (e.g. Huffman). -/
structure Compressed (α : Type _) where
  payload : List (α × Nat)
  primary : Nat
  deriving Repr

/-- Compression: BWT + RLE on the BWT output column. -/
def compress (xs : List α) : Compressed α :=
  let (last, primary) := transform xs
  { payload := rleEncode last, primary := primary }

/-- Decompression: RLE decode + inverse BWT. -/
def decompress (c : Compressed α) : List α :=
  inverse (rleDecode c.payload) c.primary

end LeanBWT
