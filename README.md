# LeanBWT

Lean 4 Burrows-Wheeler-transform utilities with a small library-style API for:

- compressing and decompressing `String` values
- compressing a file to a `.bzip2`-named payload
- decompressing that payload back into a file

## Usage

In your Lean code:

```lean
import LeanBWT
```

The root module re-exports the public API, so you can call the helpers directly from
`LeanBWT`.

## String API

```lean
import LeanBWT

open LeanBWT

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
import LeanBWT

open LeanBWT

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
import LeanBWT

open LeanBWT

def compressTo (input output : System.FilePath) : IO System.FilePath := do
  compressFile input (some output)

def decompressTo (input output : System.FilePath) : IO System.FilePath := do
  decompressFile input (some output)
```

## Important Note

The `.bzip2` output produced here is a LeanBWT-specific serialized payload built on this
project's BWT + run-length encoding pipeline. It is not intended to be byte-compatible with the
system `bzip2` tool.
