import Bzip2.BWT

set_option autoImplicit false

namespace BZip2

open Bzip2

/-- Magic header for serialized string/file payloads produced by this library. -/
def serializedMagic : String := "LEANBZIP2:1"

/-- Encode one BWT symbol into a text-safe token. -/
def encodeSymbol : Symbol Char → String
  | none => "⊥"
  | some c => s!"{c}"

/-- Decode one BWT symbol token back into a symbol. -/
def decodeSymbol? (token : String) : Except String (Symbol Char) := do
  if token = "⊥" then
    return none
  if token.length = 1 then
    return some token.front
  else
    throw s!"invalid symbol token: {token}"

/-- Serialize a character payload produced by `compress`. -/
def serializeCompressed (c : Compressed Char) : String :=
  let alpha := "".intercalate <| c.alphabet.map encodeSymbol
  let runs := ";".intercalate <| c.payload.map (fun (v, n) => s!"{v},{n}")
  "\n".intercalate [serializedMagic, toString c.primary, alpha, runs]

/-- Parse a serialized payload produced by `serializeCompressed`. -/
def deserializeCompressed? (encoded : String) : Except String (Nat × List (Symbol Char) × List (Nat × Nat)) := do
  match encoded.trimAscii.toString.splitOn "\n" with
  | [magic, rawPrimary, rawAlpha, rawRuns] =>
      if magic ≠ serializedMagic then
        throw s!"unsupported payload header: {magic}"
      let some primary := rawPrimary.toNat?
        | throw s!"invalid primary index: {rawPrimary}"
      let alpha := rawAlpha.toList.map (fun c => if c = '⊥' then none else some c)
      let parseRun (r : String) : Except String (Nat × Nat) :=
        match r.splitOn "," with
        | [rawV, rawN] => do
            let some v := rawV.toNat? | throw s!"invalid MTF index: {rawV}"
            let some n := rawN.toNat? | throw s!"invalid run length: {rawN}"
            return (v, n)
        | _ => throw s!"invalid run: {r}"
      let runs ← (rawRuns.splitOn ";").mapM parseRun
      return (primary, alpha, runs)
  | _ =>
      throw "invalid payload format: expected 4 lines"

/--
Compress a string into a serialized Bzip2 payload.
-/
def compressString (input : String) : String :=
  serializeCompressed <| Bzip2.compress input.toList

/--
Decompress a serialized Bzip2 payload back into the original string.
-/
def decompressString? (encoded : String) : Except String String := do
  let (primary, alpha, payload) ← deserializeCompressed? encoded
  let c : Compressed Char := { primary := primary, alphabet := alpha, payload := payload }
  return String.ofList <| Bzip2.decompress c

/--
Compress a `ByteArray`.
Returns the compressed data as a `ByteArray`.
-/
def compress (data : ByteArray) : ByteArray :=
  match String.fromUTF8? data with
  | some s => (compressString s).toUTF8
  | none => ByteArray.empty -- Fallback for invalid UTF-8

/--
Decompress a `ByteArray`.
-/
def decompress (data : ByteArray) : Option ByteArray :=
  match String.fromUTF8? data with
  | some s => 
      match decompressString? s with
      | .ok decompressed => some decompressed.toUTF8
      | .error _ => none
  | none => none

/-- Default output path used by `compressFile`. -/
def defaultCompressedPath (inputPath : System.FilePath) : System.FilePath :=
  inputPath.addExtension "bzip2"

/-- Default output path used by `decompressFile`. -/
def defaultDecompressedPath (inputPath : System.FilePath) : System.FilePath :=
  if inputPath.extension == some "bzip2" then
    inputPath.withExtension ""
  else
    inputPath.withExtension "out"

/--
Compress the contents of `inputPath` and write the serialized payload to `outputPath`.
-/
def compressFile (inputPath : System.FilePath) (outputPath : Option System.FilePath := none) :
    IO System.FilePath := do
  let outputPath := outputPath.getD (defaultCompressedPath inputPath)
  let contents ← IO.FS.readFile inputPath
  IO.FS.writeFile outputPath (compressString contents)
  return outputPath

/--
Decompress the serialized payload stored at `inputPath` and write the decoded text to `outputPath`.
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

end BZip2
