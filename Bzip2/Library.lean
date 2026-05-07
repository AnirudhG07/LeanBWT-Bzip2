import Bzip2.ByteCodec
import Bzip2.Format.Binary
import Bzip2.Format.BZ2

/-!
Public executable API for LeanBzip2.

This module is the main user-facing native layer:
- in-memory `ByteArray` compression/decompression,
- configurable block-size compression,
- exact `.bz2` compression/decompression,
- file helpers for both transitional `.lbz2` archives and exact `.bz2` archives,
- legacy string helpers for the original abstract serialized payload.

Important: the older transitional binary archive remains `.bz2`-inspired and
uses the `.lbz2` extension, while the exact helpers below read and write real
`.bz2` files.
-/

set_option autoImplicit false

namespace BZip2

open Bzip2

/-- Binary-safe abstract payload specialized to bytes. -/
abbrev ByteCompressed := Bzip2.ByteCompressed

/-- Compress raw bytes to the current proved abstract payload. -/
def compressPayload (data : ByteArray) : ByteCompressed :=
  Bzip2.compressBytes data

/-- Decompress the current proved abstract byte payload back to raw bytes. -/
def decompressPayload (payload : ByteCompressed) : ByteArray :=
  Bzip2.decompressBytes payload

/-- Compress raw bytes into the transitional binary-safe archive format. -/
def compressBinary? (data : ByteArray) : Except String ByteArray :=
  Bzip2.Format.compressBinary? data

/-- Compress raw bytes into a bz2-like archive using a `1`-through-`9` block-size digit. -/
def compressBinaryWithBlockSize? (blockSizeDigit : Nat) (data : ByteArray) :
    Except String ByteArray := do
  let config ← Bzip2.Format.bz2LikeConfig? blockSizeDigit
  Bzip2.Format.compressBinaryWithConfig? config data

/-- Decompress raw bytes from the transitional binary-safe archive format. -/
def decompressBinary? (archive : ByteArray) : Except String ByteArray :=
  Bzip2.Format.decompressBinary? archive

/-- Compress raw bytes into one exact `.bz2` stream using the default `BZh1` setting. -/
def compressBz2? (data : ByteArray) : Except String ByteArray :=
  Bzip2.Format.BZ2.compress? data

/-- Compress raw bytes into one exact `.bz2` stream using a `1`-through-`9` block-size digit. -/
def compressBz2WithBlockSize? (blockSizeDigit : Nat) (data : ByteArray) :
    Except String ByteArray :=
  Bzip2.Format.BZ2.compressWithBlockSize? blockSizeDigit data

/-- Decompress one or more concatenated exact `.bz2` streams. -/
def decompressBz2? (archive : ByteArray) : Except String ByteArray :=
  Bzip2.Format.BZ2.decompress? archive

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
  match compressBinary? data with
  | .ok out => out
  | .error _ => ByteArray.empty

/--
Decompress a `ByteArray`.
-/
def decompress (data : ByteArray) : Option ByteArray :=
  match decompressBinary? data with
  | .ok out => some out
  | .error _ => none

/-- Default output path used by `compressFile`. -/
def defaultCompressedPath (inputPath : System.FilePath) : System.FilePath :=
  inputPath.addExtension "lbz2"

/-- Default output path used by `compressBz2File`. -/
def defaultExactCompressedPath (inputPath : System.FilePath) : System.FilePath :=
  inputPath.addExtension "bz2"

/-- Default output path used by `decompressFile`. -/
def defaultDecompressedPath (inputPath : System.FilePath) : System.FilePath :=
  if inputPath.extension == some "lbz2" then
    inputPath.withExtension ""
  else
    inputPath.withExtension "out"

/-- Default output path used by `decompressBz2File`. -/
def defaultExactDecompressedPath (inputPath : System.FilePath) : System.FilePath :=
  if inputPath.extension == some "bz2" then
    inputPath.withExtension ""
  else
    inputPath.withExtension "out"

/--
Compress the contents of `inputPath` and write the binary archive payload to `outputPath`.
-/
def compressFile (inputPath : System.FilePath) (outputPath : Option System.FilePath := none) :
    IO System.FilePath := do
  let outputPath := outputPath.getD (defaultCompressedPath inputPath)
  let contents ← IO.FS.readBinFile inputPath
  match compressBinary? contents with
  | .ok archive =>
      IO.FS.writeBinFile outputPath archive
  | .error err =>
      throw <| IO.userError err
  return outputPath

/--
Compress the contents of `inputPath` as one exact `.bz2` stream and write the
result to `outputPath`.
-/
def compressBz2File (inputPath : System.FilePath) (outputPath : Option System.FilePath := none) :
    IO System.FilePath := do
  let outputPath := outputPath.getD (defaultExactCompressedPath inputPath)
  let contents ← IO.FS.readBinFile inputPath
  match compressBz2? contents with
  | .ok archive =>
      IO.FS.writeBinFile outputPath archive
  | .error err =>
      throw <| IO.userError err
  return outputPath

/--
Compress the contents of `inputPath` as one exact `.bz2` stream using a `1`
through `9` block-size digit, and write the result to `outputPath`.
-/
def compressBz2FileWithBlockSize
    (blockSizeDigit : Nat)
    (inputPath : System.FilePath)
    (outputPath : Option System.FilePath := none) :
    IO System.FilePath := do
  let outputPath := outputPath.getD (defaultExactCompressedPath inputPath)
  let contents ← IO.FS.readBinFile inputPath
  match compressBz2WithBlockSize? blockSizeDigit contents with
  | .ok archive =>
      IO.FS.writeBinFile outputPath archive
  | .error err =>
      throw <| IO.userError err
  return outputPath

/--
Decompress the binary archive stored at `inputPath` and write the decoded bytes to `outputPath`.
-/
def decompressFile (inputPath : System.FilePath) (outputPath : Option System.FilePath := none) :
    IO System.FilePath := do
  let outputPath := outputPath.getD (defaultDecompressedPath inputPath)
  let encoded ← IO.FS.readBinFile inputPath
  match decompressBinary? encoded with
  | .ok decoded =>
      IO.FS.writeBinFile outputPath decoded
      return outputPath
  | .error err =>
      throw <| IO.userError err

/--
Decompress one or more concatenated exact `.bz2` streams stored at `inputPath`
and write the decoded bytes to `outputPath`.
-/
def decompressBz2File (inputPath : System.FilePath) (outputPath : Option System.FilePath := none) :
    IO System.FilePath := do
  let outputPath := outputPath.getD (defaultExactDecompressedPath inputPath)
  let encoded ← IO.FS.readBinFile inputPath
  match decompressBz2? encoded with
  | .ok decoded =>
      IO.FS.writeBinFile outputPath decoded
      return outputPath
  | .error err =>
      throw <| IO.userError err

end BZip2
