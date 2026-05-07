import Mathlib

/-!
Exact `.bz2` stream model types used by the phase-1 decoder work.

These types describe the real stream header, section markers, block metadata,
and Huffman metadata that appear in Linux-compatible `.bz2` files.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

/-- 48-bit marker for a compressed block. -/
abbrev blockMagic : Nat := 0x314159265359

/-- 48-bit marker for end-of-stream. -/
abbrev endMagic : Nat := 0x177245385090

/-- Parsed `BZh<digit>` stream header. -/
structure StreamHeader where
  blockSizeDigit : Nat
  blockSizeBytes : Nat
deriving Repr, DecidableEq

/-- The next top-level section in an exact `.bz2` stream. -/
inductive SectionMarker where
  | block
  | eos
deriving Repr, DecidableEq

/-- Parsed block-local metadata before the Huffman-coded contents begin. -/
structure BlockHeader where
  blockCRC : UInt32
  randomised : Bool
  origPtr : Nat
  usedBytes : List UInt8
deriving Repr, DecidableEq

/-- Huffman table metadata encoded in an exact `.bz2` block. -/
structure HuffmanMetadata where
  groupCount : Nat
  selectors : List Nat
  codeLengths : List (List Nat)
deriving Repr, DecidableEq

/-- Parsed metadata for one compressed block. -/
structure BlockMetadata where
  header : BlockHeader
  huffman : HuffmanMetadata
deriving Repr, DecidableEq

/-- Parsed end-of-stream trailer. -/
structure EndOfStream where
  streamCRC : UInt32
deriving Repr, DecidableEq

/-- Parsed top-level section. -/
inductive Section where
  | block (metadata : BlockMetadata)
  | eos (trailer : EndOfStream)
deriving Repr, DecidableEq

/-- Exact bzip2 Huffman alphabet size for a block. -/
def BlockHeader.alphaSize (header : BlockHeader) : Nat :=
  header.usedBytes.length + 2

end Bzip2.Format.BZ2
