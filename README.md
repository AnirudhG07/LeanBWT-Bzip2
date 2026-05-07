# Bzip2

Lean 4 Bzip2 library built around a proved Burrows-Wheeler / MTF / RLE core.

Current capabilities:

- abstract BWT/MTF/RLE pipeline with correctness proofs
- byte-array compression and decompression
- `.bz2`-inspired block-stream container written as `.lbz2`
- file and in-memory APIs over that native container

> This library was made with help of Codex.

## Architecture

The codebase is now organized into four explicit layers:

- `Bzip2.Spec`
  - frozen semantic reference for the abstract BWT pipeline
  - implemented primarily in [Bzip2/BWT.lean](Bzip2/BWT.lean)
- `Bzip2.Format`
  - byte-level framing, CRCs, payload serialization, and stream structure
  - current output is `.lbz2`, not exact `.bz2`
- `Bzip2.Native`
  - executable `ByteArray` and file APIs
  - implemented primarily in [Bzip2/ByteCodec.lean](Bzip2/ByteCodec.lean) and [Bzip2/Library.lean](Bzip2/Library.lean)
- `Bzip2.Correctness`
  - stage-wise proofs and the final theorem `decompress (compress xs) = xs`

## Features and Proofs

- The BWT algorithm and its inverse are implemented and proven correct.
- Run-length encoding is implemented and proven correct.
- The full abstract compression and decompression pipeline is implemented.
- The native byte-level bridge is implemented.
- The current block-stream format has CRCs, block sizing, and concatenated-stream support.

## Dependency Boundary

- `mathlib` is used throughout the development.
- `LeanHuffmanCoding` is used in the native/format layer for Huffman codec operations.
- The semantic spec and its abstract correctness story are kept separate from the
  native container code, so future exact `.bz2` compatibility proofs can refine
  the spec layer cleanly.

## Installation

You can add this library as a dependency in `lakefile.toml` with:

```toml
[[require]]
name = "Bzip2"
git = "https://github.com/AnirudhG07/LeanBWT-Bzip2"
rev = "v4.29.0"
subDir = "bzip2"
```

For `lakefile.lean` you can use:

```
require "AnirudhG07" / "LeanBWT-Bzip2"
```

In your Lean code:

```lean
import Bzip2
```

The root module re-exports the public executable API, so you can call the
helpers directly from `Bzip2`.

## Compatibility Status

There are two distinct notions of “Bzip2” in this repo:

- abstract / proved BWT pipeline:
  - complete and proved
- exact Linux `.bz2` compatibility:
  - not complete yet

Today:

- `compressBinary?` and `compressFile` produce the project's native `.lbz2`
  format
- `decompressBinary?` and `decompressFile` read that same native format
- the format is intentionally `.bz2`-inspired, but not yet readable by system
  `bzip2` / `bunzip2`

## String API

```lean
import Bzip2

open Bzip2

def compressMessage (input : String) : String :=
  compressString input

def decompressMessage (encoded : String) : Except String String :=
  decompressString? encoded

def roundTripMessage (input : String) : Except String String := do
  let encoded := compressString input
  decompressString? encoded
```

## File API

```lean
import Bzip2

open Bzip2

def compressOnDisk (input : System.FilePath) : IO System.FilePath := do
  compressFile input

def decompressOnDisk (input : System.FilePath) : IO System.FilePath := do
  decompressFile input

def roundTripFile (input : System.FilePath) : IO System.FilePath := do
  let compressed ← compressFile input
  decompressFile compressed
```

By default:

- `compressFile "notes.txt"` writes `notes.txt.lbz2`
- `decompressFile "notes.txt.lbz2"` writes `notes.txt`

You can also pass an explicit output path:

```lean
import Bzip2

open Bzip2

def compressTo (input output : System.FilePath) : IO System.FilePath := do
  compressFile input (some output)

def decompressTo (input output : System.FilePath) : IO System.FilePath := do
  decompressFile input (some output)
```

## Native Byte API

```lean
import Bzip2

open BZip2

def roundTripBytes (input : ByteArray) : Except String ByteArray := do
  let archive ← compressBinary? input
  decompressBinary? archive
```

If you want a specific bz2-like block size:

```lean
import Bzip2

open BZip2

def roundTripBytesWithBlockSize (input : ByteArray) : Except String ByteArray := do
  let archive ← compressBinaryWithBlockSize? 1 input
  decompressBinary? archive
```

## Important Note

The current `.lbz2` output is a LeanBzip2 native format layered over the proved
BWT pipeline. It is not yet byte-compatible with the Linux `bzip2` tool.

The roadmap for exact `.bz2` compatibility and proof refinement lives in
[TODO_BZIP2_COMPAT.md](TODO_BZIP2_COMPAT.md).
