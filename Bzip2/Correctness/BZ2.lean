import Bzip2.Correctness.BZ2.Bits
import Bzip2.Correctness.BZ2.BitsReader
import Bzip2.Correctness.BZ2.ZeroRun
import Bzip2.Correctness.BZ2.RLE1
import Bzip2.Correctness.BZ2.MtfRunaRunb

/-!
# Bzip2.Correctness.BZ2

Correctness layer for the exact `.bz2` wire-format codec.

This subtree proves component-level round trips (bit IO, RLE1, RUNA/RUNB, MTF,
selectors, used-byte map, canonical Huffman) and builds toward the headline
exact stream round-trip theorem.
-/
