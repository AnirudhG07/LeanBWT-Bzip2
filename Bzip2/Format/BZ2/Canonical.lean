import Bzip2.Format.BZ2.BitReader
import Mathlib

/-!
Canonical Huffman decode tables for exact `.bz2` blocks.

Exact `.bz2` stores Huffman code lengths on the wire rather than an explicit
tree. This module rebuilds the canonical code assignments for one table and
decodes symbols directly from the bit reader.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

/-- One canonical Huffman code assignment inside an exact `.bz2` table. -/
structure CanonicalEntry where
  symbol : Nat
  bitLength : Nat
  code : Nat
deriving Repr, DecidableEq

/-- Runtime decode table reconstructed from one exact `.bz2` code-length table. -/
structure CanonicalTable where
  entries : List CanonicalEntry
  minLength : Nat
  maxLength : Nat
deriving Repr, DecidableEq

private def symbolsWithLengthAux :
    Nat → Nat → List Nat → List Nat → List Nat
  | _, _, [], acc => acc.reverse
  | index, target, len :: rest, acc =>
      let acc' := if len = target then index :: acc else acc
      symbolsWithLengthAux (index + 1) target rest acc'

private def symbolsWithLength (lengths : List Nat) (target : Nat) : List Nat :=
  symbolsWithLengthAux 0 target lengths []

private def assignEntriesAux :
    List Nat → Nat → Nat → List CanonicalEntry → List CanonicalEntry × Nat
  | [], _, nextCode, acc => (acc, nextCode)
  | sym :: rest, bitLength, nextCode, acc =>
      assignEntriesAux rest bitLength (nextCode + 1)
        ({ symbol := sym, bitLength := bitLength, code := nextCode } :: acc)

private def positiveLengths (lengths : List Nat) : List Nat :=
  lengths.filter (0 < ·)

private def minPositiveLength? : List Nat → Option Nat
  | [] => none
  | x :: xs => some (xs.foldl Nat.min x)

private def overfullEntry? (entry : CanonicalEntry) : Bool :=
  entry.code ≥ 2 ^ entry.bitLength

private def buildEntries (codeLengths : List Nat) (maxLength : Nat) : List CanonicalEntry :=
  Id.run do
    let mut entries : List CanonicalEntry := []
    let mut nextCode := 0
    for bitLength in [1:maxLength + 1] do
      if bitLength ≠ 1 then
        nextCode := nextCode * 2
      let (entries', nextCode') := assignEntriesAux (symbolsWithLength codeLengths bitLength) bitLength nextCode entries
      entries := entries'
      nextCode := nextCode'
    pure entries.reverse

/-- Rebuild one exact `.bz2` canonical Huffman table from decoded code lengths. -/
def CanonicalTable.build (codeLengths : List Nat) : Except String CanonicalTable := do
  let positive := positiveLengths codeLengths
  let some minLength := minPositiveLength? positive
    | throw "Exact `.bz2` Huffman table contains no symbols."
  let maxLength := positive.foldl Nat.max 0
  if positive.any (fun len => 20 < len) then
    throw "Exact `.bz2` Huffman code length exceeds the supported limit."
  let entries := buildEntries codeLengths maxLength
  if entries.any overfullEntry? then
    throw "Exact `.bz2` Huffman table is overfull."
  pure
    { entries := entries
    , minLength := minLength
    , maxLength := maxLength
    }

private def lookupEntry? (entries : List CanonicalEntry) (bitLength code : Nat) : Option Nat :=
  (entries.find? (fun entry => entry.bitLength = bitLength ∧ entry.code = code)).map (·.symbol)

private def decodeSymbolAux
    (fuel : Nat) (table : CanonicalTable) (bitLength code : Nat) (reader : BitReader) :
    Except String (Nat × BitReader) :=
  match fuel with
  | 0 =>
      throw "Exact `.bz2` Huffman stream does not match the current canonical table."
  | fuel + 1 => do
      let (bit, reader') ← reader.readBit
      let bitLength' := bitLength + 1
      let code' := code * 2 + if bit then 1 else 0
      if table.minLength ≤ bitLength' then
        match lookupEntry? table.entries bitLength' code' with
        | some symbol => pure (symbol, reader')
        | none => decodeSymbolAux fuel table bitLength' code' reader'
      else
        decodeSymbolAux fuel table bitLength' code' reader'
termination_by fuel

/-- Decode one exact `.bz2` symbol from a canonical Huffman table. -/
def CanonicalTable.decodeSymbol (table : CanonicalTable) (reader : BitReader) :
    Except String (Nat × BitReader) :=
  decodeSymbolAux table.maxLength table 0 0 reader

end Bzip2.Format.BZ2
