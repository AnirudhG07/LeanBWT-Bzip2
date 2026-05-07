import Bzip2.Format.BZ2.Model
import Bzip2.Format.BZ2.BitReader
import Bzip2.Format.BZ2.BitWriter
import Bzip2.Format.BZ2.Parser
import Bzip2.Format.BZ2.Canonical
import Bzip2.Format.BZ2.CRC
import Bzip2.Format.BZ2.InverseBWT
import Bzip2.Format.BZ2.Transform
import Bzip2.Format.BZ2.Decoder
import Bzip2.Format.BZ2.Encoder

/-!
# Bzip2.Format.BZ2

Exact `.bz2` decoding subtree for the ongoing phase-1 compatibility work.

This namespace is the professional home for Linux-compatible `.bz2` support:
metadata parsing, exact block transforms, canonical Huffman coding, checksum
validation, and exact stream compression/decompression.
-/
