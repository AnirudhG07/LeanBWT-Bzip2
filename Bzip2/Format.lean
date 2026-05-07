import Bzip2.Format.Bytes
import Bzip2.Format.CRC32
import Bzip2.Format.Payload
import Bzip2.Format.HuffmanArchive
import Bzip2.Format.Binary

/-!
# Bzip2.Format

Byte-level container and stream-format layer.

Today this layer provides the project's `.bz2`-inspired native-on-disk format:
block framing, CRCs, block payload serialization, and Huffman-backed archive
packing. The current output is `.lbz2` and is not yet exact `.bz2`.
-/
