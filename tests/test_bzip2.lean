import Bzip2

def byteArrayOfList (xs : List UInt8) : ByteArray :=
  xs.foldl ByteArray.push ByteArray.empty

private def bumpByte (b : UInt8) : UInt8 :=
  UInt8.ofNat (b.toNat + 1)

private def overwriteAt : Nat → (UInt8 → UInt8) → List UInt8 → List UInt8
  | _, _, [] => []
  | 0, f, b :: bs => f b :: bs
  | n + 1, f, b :: bs => b :: overwriteAt n f bs

/--
Corrupt the first byte of the embedded Huffman payload.
The top-level archive header is 13 bytes long:
`magic(4) | version(1) | rawLen(u32) | crc(u32) | packedLen(u32)`.
-/
def corruptPackedPayload (bytes : ByteArray) : ByteArray :=
  byteArrayOfList <| overwriteAt 13 bumpByte bytes.toList

def binaryTest : IO Unit := do
  let input := "The quick brown fox jumps over the lazy dog".toUTF8
  match compressBinary? input with
  | .error err =>
      IO.println s!"Binary test failed during compression: {err}"
  | .ok archive =>
      match decompressBinary? archive with
      | .error err =>
          IO.println s!"Binary test failed during decompression: {err}"
      | .ok output =>
          if output == input then
            IO.println "Binary roundtrip passed"
          else
            IO.println "Binary roundtrip failed"

def corruptionTest : IO Unit := do
  let input := "Corruption detection should reject damaged archives".toUTF8
  match compressBinary? input with
  | .error err =>
      IO.println s!"Corruption test failed during compression: {err}"
  | .ok archive =>
      let corrupted := corruptPackedPayload archive
      match decompressBinary? corrupted with
      | .ok _ =>
          IO.println "Corruption test failed: damaged archive unexpectedly decoded"
      | .error _ =>
          IO.println "Corruption test passed"

def stringTest : IO Unit := do
  let input := "The quick brown fox jumps over the lazy dog"
  let compressed := compressString input
  IO.println s!"Input: {input}"
  match decompressString? compressed with
  | .ok decompressed =>
      IO.println s!"Decompressed: {decompressed}"
      if input == decompressed then
        IO.println "Test passed"
      else
        IO.println "Test failed: mismatch"
  | .error err =>
      IO.println s!"Test failed: {err}"

def fileTest : IO Unit := do
  let input := "The quick brown fox jumps over the lazy dog"
  -- File test
  let testFile : System.FilePath := "test_file.txt"
  IO.FS.writeFile testFile input
  let compressedFile ← compressFile testFile
  let decompressedFile ← decompressFile compressedFile (some "test_file_out.txt")
  let decompressedText ← IO.FS.readFile decompressedFile
  if input == decompressedText then
    IO.println "File roundtrip passed"
  else
    IO.println "File roundtrip failed"

  -- Cleanup
  IO.FS.removeFile testFile
  IO.FS.removeFile compressedFile
  IO.FS.removeFile decompressedFile

def main : IO Unit := do
  IO.println "Running binary test..."
  binaryTest
  IO.println "\nRunning corruption test..."
  corruptionTest
  IO.println "\nRunning string test..."
  stringTest
  IO.println "\nRunning file test..."
  fileTest
