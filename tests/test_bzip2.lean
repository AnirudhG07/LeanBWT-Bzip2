import Bzip2
import Bzip2.Format.Binary

def byteArrayOfList (xs : List UInt8) : ByteArray :=
  xs.foldl ByteArray.push ByteArray.empty

private def bumpByte (b : UInt8) : UInt8 :=
  UInt8.ofNat (b.toNat + 1)

private def overwriteAt : Nat → (UInt8 → UInt8) → List UInt8 → List UInt8
  | _, _, [] => []
  | 0, f, b :: bs => f b :: bs
  | n + 1, f, b :: bs => b :: overwriteAt n f bs

/--
Corrupt the first byte of the first block payload in the bz2-like archive.
The prefix before block payload bytes is:
`BZh(4) | blockMagic(6) | blockCRC(u32) | rawLen(u32) | packedLen(u32)`.
-/
def corruptPackedPayload (bytes : ByteArray) : ByteArray :=
  byteArrayOfList <| overwriteAt 22 bumpByte bytes.toList

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

def multiBlockTest : IO Unit := do
  let config : Bzip2.Format.StreamConfig :=
    { blockSizeDigit := 1, blockBytes := 32 }
  let input :=
    byteArrayOfList <| (List.range 192).map (fun n => UInt8.ofNat (n % 251))
  match Bzip2.Format.compressBinaryWithConfig? config input with
  | .error err =>
      IO.println s!"Multi-block test failed during compression: {err}"
  | .ok archive =>
      match decompressBinary? archive with
      | .error err =>
          IO.println s!"Multi-block test failed during decompression: {err}"
      | .ok output =>
          if output == input then
            IO.println "Multi-block roundtrip passed"
          else
            IO.println "Multi-block roundtrip failed"

def concatenatedStreamTest : IO Unit := do
  let left := "left stream".toUTF8
  let right := "right stream".toUTF8
  match compressBinary? left, compressBinary? right with
  | .ok leftArchive, .ok rightArchive =>
      let concatenated := byteArrayOfList (leftArchive.toList ++ rightArchive.toList)
      match decompressBinary? concatenated with
      | .error err =>
          IO.println s!"Concatenated-stream test failed during decompression: {err}"
      | .ok output =>
          let expected := byteArrayOfList (left.toList ++ right.toList)
          if output == expected then
            IO.println "Concatenated-stream test passed"
          else
            IO.println "Concatenated-stream test failed"
  | .error err, _ =>
      IO.println s!"Concatenated-stream test failed during first compression: {err}"
  | _, .error err =>
      IO.println s!"Concatenated-stream test failed during second compression: {err}"

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
  IO.println "\nRunning multi-block test..."
  multiBlockTest
  IO.println "\nRunning concatenated-stream test..."
  concatenatedStreamTest
  IO.println "\nRunning string test..."
  stringTest
  IO.println "\nRunning file test..."
  fileTest
