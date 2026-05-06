import LeanBWT.BWT
import LeanBWT.Library
import LeanBWT.BwtCorrectness

/-!
# LeanBWT

Import `LeanBWT` to get the full public API:

- core Burrows-Wheeler transform and RLE definitions from `LeanBWT.BWT`
- library-friendly string and file helpers from `LeanBWT.Library`

Typical usage:

```lean
import LeanBWT

open LeanBWT

def roundTripString (input : String) : Except String String := do
  let encoded := compressString input
  decompressString? encoded

def roundTripFile (path : System.FilePath) : IO System.FilePath := do
  let compressed ← compressFile path
  decompressFile compressed
```
-/
