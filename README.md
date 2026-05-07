# Bzip2

Lean 4 Bzip2 Library from Burrows-Wheeler-transformation.

- compressing and decompressing `String` values
- compressing a file to a `.bzip2`-named payload
- decompressing that payload back into a file

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

The root module re-exports the public API, so you can call the helpers directly from
`Bzip2`.

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

- `compressFile "notes.txt"` writes `notes.txt.bzip2`
- `decompressFile "notes.txt.bzip2"` writes `notes.txt`

You can also pass an explicit output path:

```lean
import Bzip2

open Bzip2

def compressTo (input output : System.FilePath) : IO System.FilePath := do
  compressFile input (some output)

def decompressTo (input output : System.FilePath) : IO System.FilePath := do
  decompressFile input (some output)
```

## Important Note

The `.bzip2` output produced here is a Bzip2 specific serialized payload built on this
project's BWT + run-length encoding pipeline. It is not YET to be byte-compatible with the
system `bzip2` tool.
