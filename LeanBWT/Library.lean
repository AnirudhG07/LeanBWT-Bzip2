import LeanBWT.BWT

namespace LeanBWT

set_option autoImplicit false

/--
Default extension used by the library file helpers.

Note: this stores a LeanBWT-specific serialized payload, not a byte-compatible GNU `bzip2` stream.
-/
def compressedFileSuffix : String := ".bzip2"

/-- Magic header for serialized string/file payloads produced by this library. -/
def serializedMagic : String := "LEANBWT:1"

/-- Encode one BWT symbol into a text-safe token. -/
def encodeSymbol : Symbol Char → String
  | none => "bot"
  | some c => s!"chr:{c.toNat}"

/-- Decode one BWT symbol token back into a symbol. -/
def decodeSymbol? (token : String) : Except String (Symbol Char) := do
  if token = "bot" then
    return none
  match token.splitOn ":" with
  | ["chr", rawCode] =>
      let some code := rawCode.toNat?
        | throw s!"invalid character code: {rawCode}"
      let c := Char.ofNat code
      if c.toNat = code then
        return some c
      else
        throw s!"invalid Unicode scalar value: {code}"
  | _ =>
      throw s!"invalid symbol token: {token}"

/-- Encode one run-length entry into a text-safe token. -/
def encodeRun (run : Symbol Char × Nat) : String :=
  s!"{encodeSymbol run.1}@{run.2}"

/-- Decode one run-length entry from a serialized token. -/
def decodeRun? (token : String) : Except String (Symbol Char × Nat) := do
  match token.splitOn "@" with
  | [rawSymbol, rawCount] =>
      let symbol ← decodeSymbol? rawSymbol
      let some count := rawCount.toNat?
        | throw s!"invalid run length: {rawCount}"
      return (symbol, count)
  | _ =>
      throw s!"invalid run token: {token}"

/-- Serialize a character payload produced by `compress`. -/
def serializeCompressed (c : Compressed Char) : String :=
  let runs := ";".intercalate <| c.payload.map encodeRun
  "\n".intercalate [serializedMagic, toString c.bwt.primary, runs]

/-- Parse a serialized payload produced by `serializeCompressed`. -/
def deserializeCompressed? (encoded : String) : Except String (Nat × List (Symbol Char × Nat)) := do
  match encoded.trimAscii.toString.splitOn "\n" with
  | [magic, rawPrimary, rawRuns] =>
      if magic ≠ serializedMagic then
        throw s!"unsupported payload header: {magic}"
      let some primary := rawPrimary.toNat?
        | throw s!"invalid primary index: {rawPrimary}"
      let runs ← (rawRuns.splitOn ";").mapM decodeRun?
      return (primary, runs)
  | _ =>
      throw "invalid payload format: expected 3 lines"

/--
Compress a string into a serialized LeanBWT payload.

The returned string is suitable for storing in a `.bzip2` file via `compressFile`.
-/
def compressString (input : String) : String :=
  serializeCompressed <| compress input.toList

/--
Decompress a serialized LeanBWT payload back into the original string.

Returns a descriptive error if the payload cannot be parsed.
-/
def decompressString? (encoded : String) : Except String String := do
  let (primary, payload) ← deserializeCompressed? encoded
  let last := rleDecode payload
  return String.ofList <| inverseFromLast last primary

/-- Default output path used by `compressFile`. -/
def defaultCompressedPath (inputPath : System.FilePath) : System.FilePath :=
  System.FilePath.mk (inputPath.toString ++ compressedFileSuffix)

def getFileWithoutExtension (path : System.FilePath)
  (extension : Option String := compressedFileSuffix) : String :=
  let name := path.fileName.getD ""
  match name.splitOn "." with
  | [] => name
  | [_] => name
  | parts => String.intercalate "." (parts.dropLast)

/-- Default output path used by `decompressFile`. -/
def defaultDecompressedPath (inputPath : System.FilePath) : System.FilePath :=
  if inputPath.toString.endsWith compressedFileSuffix then
    inputPath.withExtension ""
  else
    System.FilePath.mk (inputPath.toString ++ ".out")

/--
Compress the contents of `inputPath` and write the serialized payload to `outputPath`.

If `outputPath` is omitted, the library writes to `inputPath ++ ".bzip2"`.
-/
def compressFile (inputPath : System.FilePath) (outputPath : Option System.FilePath := none) :
    IO System.FilePath := do
  let outputPath := outputPath.getD (defaultCompressedPath inputPath)
  let contents ← IO.FS.readFile inputPath
  IO.FS.writeFile outputPath (compressString contents)
  return outputPath

/--
Decompress the serialized payload stored at `inputPath` and write the decoded text to `outputPath`.

If `outputPath` is omitted, the library strips a trailing `.bzip2` extension when present.
-/
def decompressFile (inputPath : System.FilePath) (outputPath : Option System.FilePath := none) :
    IO System.FilePath := do
  let outputPath := outputPath.getD (defaultDecompressedPath inputPath)
  let encoded ← IO.FS.readFile inputPath
  match decompressString? encoded with
  | .ok decoded =>
      IO.FS.writeFile outputPath decoded
      return outputPath
  | .error err =>
      throw <| IO.userError err

end LeanBWT
