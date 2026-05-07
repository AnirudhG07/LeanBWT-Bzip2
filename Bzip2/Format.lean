import Bzip2.Format.Bytes
import Bzip2.Format.CRC32
import Bzip2.Format.Payload
import Bzip2.Format.HuffmanArchive
import Bzip2.Format.Binary
import Bzip2.Format.BZ2

/-!
# Bzip2.Format

Byte-level container and stream-format layer.

Today this layer provides both:
- the project's older `.bz2`-inspired `.lbz2` container, and
- the exact `.bz2` compression/decompression subtree.

The transitional `.lbz2` format remains for the proved abstract pipeline,
while `Bzip2.Format.BZ2` now owns Linux-compatible exact stream handling.
-/
