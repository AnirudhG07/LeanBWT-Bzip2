import Bzip2.Format.BZ2.CRC
import Bzip2.Format.BZ2.Canonical
import Bzip2.Format.BZ2.InverseBWT
import Bzip2.Format.BZ2.Parser
import Bzip2.Format.Bytes

/-!
Executable exact `.bz2` decoder.

This module turns the parsed exact stream metadata into real decoded bytes for
Linux-compatible `.bz2` files:
- canonical Huffman decoding,
- RUNA/RUNB expansion,
- inverse MTF,
- standard inverse BWT,
- final initial-RLE reconstruction,
- per-block and per-stream CRC validation.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

private def appendByteArray (left right : ByteArray) : ByteArray :=
  right.foldl ByteArray.push left

private def prependCopies : UInt8 → Nat → List UInt8 → List UInt8
  | _, 0, acc => acc
  | byte, n + 1, acc => prependCopies byte n (byte :: acc)

private def decodeMTFIndex (alphabet : List UInt8) (index : Nat) :
    Except String (UInt8 × List UInt8) := do
  match alphabet[index]? with
  | none => throw "Exact `.bz2` MTF index is outside the used-byte alphabet."
  | some byte => pure (byte, byte :: alphabet.erase byte)

private def flushRepeat
    (alphabet : List UInt8) (repeatCount outCount maxBlockSize : Nat) (outRev : List UInt8) :
    Except String (Nat × List UInt8) := do
  if repeatCount = 0 then
    pure (outCount, outRev)
  else
    let some byte := alphabet.head?
      | throw "Exact `.bz2` RUNA/RUNB sequence referenced an empty MTF alphabet."
    if maxBlockSize < outCount + repeatCount then
      throw "Exact `.bz2` block expands past the declared block size."
    pure (outCount + repeatCount, prependCopies byte repeatCount outRev)

private structure GroupState where
  currentTable : CanonicalTable
  nextSelectorIndex : Nat
  decodedInGroup : Nat

private def initGroupState
    (tables : List CanonicalTable) (selectors : List Nat) : Except String GroupState := do
  let some firstSelector := selectors[0]?
    | throw "Exact `.bz2` block does not contain any Huffman selectors."
  let some firstTable := tables[firstSelector]?
    | throw "Exact `.bz2` selector references a missing Huffman table."
  pure
    { currentTable := firstTable
    , nextSelectorIndex := 1
    , decodedInGroup := 0
    }

private def decodeNextSymbol
    (tables : List CanonicalTable) (selectors : List Nat)
    (groupState : GroupState) (reader : BitReader) :
    Except String (Nat × GroupState × BitReader) := do
  let groupState ←
    if groupState.decodedInGroup = 50 then
      let some selector := selectors[groupState.nextSelectorIndex]?
        | throw "Exact `.bz2` block ran out of Huffman selectors."
      let some table := tables[selector]?
        | throw "Exact `.bz2` selector references a missing Huffman table."
      pure
        { currentTable := table
        , nextSelectorIndex := groupState.nextSelectorIndex + 1
        , decodedInGroup := 0
        }
    else
      pure groupState
  let (symbol, reader') := ← groupState.currentTable.decodeSymbol reader
  pure
    ( symbol
    , { groupState with decodedInGroup := groupState.decodedInGroup + 1 }
    , reader'
    )

private partial def decodeLastColumnLoop
    (maxBlockSize endOfBlock : Nat) (tables : List CanonicalTable) (selectors : List Nat)
    (alphabet : List UInt8) (groupState : GroupState) (reader : BitReader)
    (repeatCount repeatPower outCount : Nat) (outRev : List UInt8) :
    Except String (ByteArray × BitReader) := do
  let (symbol, groupState', reader') ← decodeNextSymbol tables selectors groupState reader
  if symbol < 2 then
    let repeatPower' := if repeatCount = 0 then 1 else repeatPower
    let repeatCount' := repeatCount + repeatPower' * if symbol = 0 then 1 else 2
    if 2 * 1024 * 1024 < repeatCount' then
      throw "Exact `.bz2` RUNA/RUNB repeat count is unrealistically large."
    decodeLastColumnLoop maxBlockSize endOfBlock tables selectors alphabet groupState'
      reader' repeatCount' (repeatPower' * 2) outCount outRev
  else
    let (outCount', outRev') ← flushRepeat alphabet repeatCount outCount maxBlockSize outRev
    if symbol = endOfBlock then
      pure (Bzip2.Format.byteArrayOfList outRev'.reverse, reader')
    else
      let (byte, alphabet') ← decodeMTFIndex alphabet (symbol - 1)
      if maxBlockSize < outCount' + 1 then
        throw "Exact `.bz2` block exceeds the declared block size."
      decodeLastColumnLoop maxBlockSize endOfBlock tables selectors alphabet' groupState'
        reader' 0 0 (outCount' + 1) (byte :: outRev')

private def decodeLastColumn
    (maxBlockSize : Nat) (header : BlockHeader) (huffman : HuffmanMetadata) (reader : BitReader) :
    Except String (ByteArray × BitReader) := do
  if header.usedBytes.isEmpty then
    throw "Exact `.bz2` block uses an empty byte alphabet."
  let tables ← huffman.codeLengths.mapM CanonicalTable.build
  let groupState ← initGroupState tables huffman.selectors
  let endOfBlock := header.usedBytes.length + 1
  decodeLastColumnLoop maxBlockSize endOfBlock tables huffman.selectors header.usedBytes
    groupState reader 0 0 0 []

private def decodeInitialRLE (input : ByteArray) : ByteArray :=
  Id.run do
    let mut out := ByteArray.empty
    let mut i := 0
    while i < input.size do
      let byte := input[i]!
      if i + 4 < input.size
          && input[i + 1]! = byte
          && input[i + 2]! = byte
          && input[i + 3]! = byte then
        out := out.push byte
        out := out.push byte
        out := out.push byte
        out := out.push byte
        let repeats := input[i + 4]!.toNat
        for _ in [0:repeats] do
          out := out.push byte
        i := i + 5
      else
        out := out.push byte
        i := i + 1
    pure out

private def decodeBlockAfterMetadata
    (maxBlockSize : Nat) (metadata : BlockMetadata) (reader : BitReader) :
    Except String (ByteArray × UInt32 × BitReader) := do
  if metadata.header.randomised then
    throw "Exact `.bz2` decoder does not support deprecated randomised blocks."
  let (lastColumn, reader1) ← decodeLastColumn maxBlockSize metadata.header metadata.huffman reader
  let preRLE ← inverseBWT lastColumn metadata.header.origPtr
  let decoded := decodeInitialRLE preRLE
  let blockCRC := crc32 decoded
  if blockCRC ≠ metadata.header.blockCRC then
    throw "Exact `.bz2` block CRC mismatch."
  pure (decoded, blockCRC, reader1)

private partial def decodeSections
    (header : StreamHeader) (reader : BitReader) (streamCRC : UInt32) (out : ByteArray) :
    Except String (ByteArray × BitReader) := do
  let (marker, reader1) ← parseSectionMarker reader
  match marker with
  | .block =>
      let (metadata, reader2) ← parseBlockSectionAfterMarker reader1
      let (decoded, blockCRC, reader3) ← decodeBlockAfterMetadata header.blockSizeBytes metadata reader2
      let streamCRC' := combineStreamCRC streamCRC blockCRC
      decodeSections header reader3 streamCRC' (appendByteArray out decoded)
  | .eos =>
      let (trailer, reader2) ← parseEndOfStreamAfterMarker reader1
      if trailer.streamCRC ≠ streamCRC then
        throw "Exact `.bz2` stream CRC mismatch."
      pure (out, reader2.alignToByte)

private partial def decodeStreams (reader : BitReader) (out : ByteArray) :
    Except String ByteArray := do
  let reader := reader.alignToByte
  if reader.bitsRemaining = 0 then
    pure out
  else
    let (header, reader1) ← parseStreamHeader reader
    let (streamBytes, reader2) ← decodeSections header reader1 0 ByteArray.empty
    decodeStreams reader2 (appendByteArray out streamBytes)

/-- Decompress one or more concatenated exact `.bz2` streams. -/
def decompress? (archive : ByteArray) : Except String ByteArray :=
  decodeStreams (BitReader.ofByteArray archive) ByteArray.empty

private partial def decodeSectionsToHandle
    (header : StreamHeader) (reader : BitReader) (streamCRC : UInt32)
    (handle : IO.FS.Handle) :
    IO (Except String BitReader) := do
  match parseSectionMarker reader with
  | .error err => pure (.error err)
  | .ok (.block, reader1) =>
      match parseBlockSectionAfterMarker reader1 with
      | .error err => pure (.error err)
      | .ok (metadata, reader2) =>
          match decodeBlockAfterMetadata header.blockSizeBytes metadata reader2 with
          | .error err => pure (.error err)
          | .ok (decoded, blockCRC, reader3) =>
              handle.write decoded
              let streamCRC' := combineStreamCRC streamCRC blockCRC
              decodeSectionsToHandle header reader3 streamCRC' handle
  | .ok (.eos, reader1) =>
      match parseEndOfStreamAfterMarker reader1 with
      | .error err => pure (.error err)
      | .ok (trailer, reader2) =>
          if trailer.streamCRC ≠ streamCRC then
            pure (.error "Exact `.bz2` stream CRC mismatch.")
          else
            pure (.ok reader2.alignToByte)

private partial def decodeStreamsToHandle
    (reader : BitReader) (handle : IO.FS.Handle) :
    IO (Except String Unit) := do
  let reader := reader.alignToByte
  if reader.bitsRemaining = 0 then
    pure (.ok ())
  else
    match parseStreamHeader reader with
    | .error err => pure (.error err)
    | .ok (header, reader1) =>
        match ← decodeSectionsToHandle header reader1 0 handle with
        | .error err => pure (.error err)
        | .ok reader2 => decodeStreamsToHandle reader2 handle

/--
Decompress one or more concatenated exact `.bz2` streams and write the decoded
bytes directly to a file handle block by block.
-/
def decompressToHandle? (archive : ByteArray) (handle : IO.FS.Handle) :
    IO (Except String Unit) :=
  decodeStreamsToHandle (BitReader.ofByteArray archive) handle

end Bzip2.Format.BZ2
