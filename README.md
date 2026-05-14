# Bzip2

Lean 4 Bzip2 library built around a proved Burrows-Wheeler / MTF / RLE core,
with a practical `.bz2` execution path alongside the original reference
construction.

> [!Note]
> This project is a work in progress. The original BWT pipeline is proved, the
> exact `.bz2` path interoperates with Linux `bzip2`, and the next major step is
> to add a separate fast native BWT implementation while keeping the original
> proved construction intact.

## Two BWT Layers

This project intentionally keeps **two different roles** for BWT:

### 1. Reference / Proved BWT

- This is the original BWT construction developed in Lean.
- It is the mathematical specification for the project.
- Its proofs are kept as the long-term correctness anchor.
- It is not being deleted or replaced.

This layer is where we want clarity and proof structure, not raw performance.

### 2. Practical / Native BWT

- This is the execution-oriented path used by the compressor/decompressor.
- Today, the exact `.bz2` implementation is already wired and interoperable for
  practical small/medium inputs.
- A separate fast forward-BWT runtime module now exists for the exact encoder.
- The next performance milestone is to extend that split into the broader fast
  BWT / inverse-BWT path needed for larger-scale practical workloads.

The long-term plan is:

- keep the original BWT as the reference semantics,
- use the fast BWT in the runtime path,
- prove the fast BWT correct by refinement against the original BWT.

## Architecture

The codebase is now organized into four explicit layers:

- `Bzip2.Spec`
  - frozen semantic reference for the abstract BWT pipeline
  - home of the original proved BWT / inverse-BWT story
  - implemented primarily in [Bzip2/BWT.lean](Bzip2/BWT.lean)
- `Bzip2.Format`
  - byte-level framing, CRCs, payload serialization, and stream structure
  - includes both the older `.lbz2` path and the exact `.bz2` wire format
- `Bzip2.Native`
  - executable `ByteArray` and file APIs
  - implemented primarily in [Bzip2/ByteCodec.lean](Bzip2/ByteCodec.lean) and [Bzip2/Library.lean](Bzip2/Library.lean)
- `Bzip2.Correctness`
  - stage-wise proofs and the final theorem `decompress (compress xs) = xs`

## Current Construction vs Practical Path

### Original proved construction

- Abstract BWT, inverse BWT, MTF, and RLE are proved correct.
- This is the reference pipeline we want all later implementations to agree
  with.
- It is the right place to understand the mathematics of the transform.

### Practical executable path

- There is a byte-oriented runtime API.
- There is an exact `.bz2` encoder/decoder interoperable with Linux `bzip2` and
  `bunzip2` for practical small/medium cases.
- The exact encoder now uses a separate fast forward-BWT runtime module rather
  than the original proof-oriented construction.
- There is also an older `.lbz2` transitional format retained for the abstract
  pipeline.

### Planned fast BWT path

- We now have the first separate fast forward-BWT implementation for the exact
  runtime path.
- It will live **alongside** the original proved construction.
- The executable compressor/decompressor should eventually use this fast path by
  default.
- A later proof layer will show that the fast path refines the original proved
  BWT semantics.

## Features and Proofs

- The BWT algorithm and its inverse are implemented and proven correct.
- Run-length encoding is implemented and proven correct.
- The full abstract compression and decompression pipeline is implemented.
- The native byte-level bridge is implemented.
- The exact `.bz2` path has CRCs, block sizing, concatenated-stream support,
  and Linux interoperability tests.
- Robustness tests cover malformed exact streams and corrupted data.
- Large-file exact support is still gated on further work: a broader fast native
  BWT / inverse-BWT path plus more practical large-block streaming behavior.

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

### Dependencies

- `mathlib` is used throughout the development.
- `LeanHuffmanCoding` is used in the native/format layer for Huffman codec operations.

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

def compressLegacyOnDisk (input : System.FilePath) : IO System.FilePath := do
  compressFile input

def decompressLegacyOnDisk (input : System.FilePath) : IO System.FilePath := do
  decompressFile input

def roundTripLegacyFile (input : System.FilePath) : IO System.FilePath := do
  let compressed ← compressFile input
  decompressFile compressed

def compressExactOnDisk (input : System.FilePath) : IO System.FilePath := do
  compressBz2File input

def decompressExactOnDisk (input : System.FilePath) : IO System.FilePath := do
  decompressBz2File input
```

By default:

- `compressFile "notes.txt"` writes `notes.txt.lbz2`
- `decompressFile "notes.txt.lbz2"` writes `notes.txt`
- `compressBz2File "notes.txt"` writes `notes.txt.bz2`
- `decompressBz2File "notes.txt.bz2"` writes `notes.txt`

You can also pass an explicit output path:

```lean
import Bzip2

open Bzip2

def compressTo (input output : System.FilePath) : IO System.FilePath := do
  compressFile input (some output)

def decompressTo (input output : System.FilePath) : IO System.FilePath := do
  decompressFile input (some output)

def compressExactTo (input output : System.FilePath) : IO System.FilePath := do
  compressBz2File input (some output)

def decompressExactTo (input output : System.FilePath) : IO System.FilePath := do
  decompressBz2File input (some output)
```

## Native Byte API

```lean
import Bzip2

open BZip2

def roundTripBytes (input : ByteArray) : Except String ByteArray := do
  let archive ← compressBinary? input
  decompressBinary? archive

-- If you want a specific bz2-like block size:
def roundTripBytesWithBlockSize (input : ByteArray) : Except String ByteArray := do
  let archive ← compressBinaryWithBlockSize? 1 input
  decompressBinary? archive
```

## Testing

You can run the tests in `tests/` with:

```bash
lake env lean --run tests/test_bzip2_<NAME>.lean
```

Important test entry points:

- `tests/test_bzip2_format.lean`
  - main mixed-format suite
- `tests/test_bz2_exact.lean`
  - exact `.bz2` decode / encode checks
- `tests/test_bzip2_shell.lean`
  - shell-level checks against Linux `bzip2`
- `tests/test_bzip2_large.lean`
  - opt-in large/stress harness

The large harness is intentionally gated because the current exact runtime still
needs the future fast native BWT implementation before large exact workloads are
honest to run by default.

## Acknowledgements
This library was made with help of Codex, however not all code was generated by Codex and some was written by hand.
