import Bzip2

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
  IO.println "Running string test..."
  stringTest
  IO.println "\nRunning file test..."
  fileTest
