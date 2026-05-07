import Bzip2.Spec
import Bzip2.Format
import Bzip2.Native
import Bzip2.Correctness

/-!
# Bzip2

Top-level entrypoint for the project.

Architecture:
- `Bzip2.Spec`: frozen semantic BWT/MTF/RLE model.
- `Bzip2.Format`: byte-level container and stream-format modules.
- `Bzip2.Native`: executable byte-array and file APIs.
- `Bzip2.Correctness`: proof layer for the abstract pipeline.

Current status:
- the semantic core is proved correct,
- the native archive format is `.bz2`-inspired and written as `.lbz2`,
- exact Linux `bzip2` interoperability is still in progress.
-/

export BZip2 (compress decompress compressString decompressString? compressFile decompressFile)
export BZip2 (compressBinary? compressBinaryWithBlockSize? decompressBinary? decompressBz2? compressPayload decompressPayload)
