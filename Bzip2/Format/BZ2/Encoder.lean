import Bzip2.Format.BZ2.BitWriter
import Bzip2.Format.BZ2.CRC
import Bzip2.Format.BZ2.Canonical
import Bzip2.Format.BZ2.Model
import Bzip2.Format.BZ2.Transform
import Huffman.Codec

/-!
Executable exact `.bz2` encoder.

This module emits Linux-compatible `.bz2` streams using the exact wire format:
- initial RLE1 plus standard `origPtr`-based BWT,
- used-byte bitmap and MTF/RUNA/RUNB payload coding,
- canonical Huffman code lengths and selectors,
- block markers, per-block CRCs, and the stream trailer CRC.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

/-- Exact `.bz2` stream configuration. -/
structure StreamConfig where
  blockSizeDigit : Nat
  blockSizeBytes : Nat
deriving Inhabited, Repr

/-- Default exact `.bz2` stream configuration: `BZh1`. -/
def defaultStreamConfig : StreamConfig :=
  { blockSizeDigit := 1, blockSizeBytes := 100000 }

/-- Incremental exact `.bz2` encoder state for file-oriented block processing. -/
structure StreamEncoderState where
  writer : BitWriter
  streamCRC : UInt32

/-- Build an exact `.bz2` configuration from the usual `1`-through-`9` digit. -/
def streamConfig? (blockSizeDigit : Nat) : Except String StreamConfig := do
  if 1 ≤ blockSizeDigit ∧ blockSizeDigit ≤ 9 then
    pure
      { blockSizeDigit := blockSizeDigit
      , blockSizeBytes := blockSizeDigit * 100000
      }
  else
    throw "Exact `.bz2` block size digit must be between 1 and 9."

private def bitMaskAt (index : Nat) : Nat :=
  2 ^ (15 - index)

private def groupMask (group : Nat) (usedBytes : List UInt8) : Nat :=
  (List.range 16).foldl
    (fun acc offset =>
      if UInt8.ofNat (group * 16 + offset) ∈ usedBytes then
        acc + bitMaskAt offset
      else
        acc)
    0

private def groupsBitmap (usedBytes : List UInt8) : Nat :=
  (List.range 16).foldl
    (fun acc group =>
      if groupMask group usedBytes = 0 then
        acc
      else
        acc + bitMaskAt group)
    0

private def moveToFrontValue (value : Nat) (xs : List Nat) : Except String (Nat × List Nat) := do
  let index := xs.findIdx (· = value)
  match xs[index]? with
  | none => throw "Exact `.bz2` selector MTF encoding lost a Huffman-group value."
  | some _ => pure (index, value :: xs.erase value)

private def encodeSelectorsAux :
    List Nat → List Nat → List Nat → Except String (List Nat)
  | [], _, acc => pure acc.reverse
  | selector :: rest, mtf, acc => do
      let (encoded, mtf') ← moveToFrontValue selector mtf
      encodeSelectorsAux rest mtf' (encoded :: acc)

private def encodeSelectors (groupCount : Nat) (selectors : List Nat) : Except String (List Nat) :=
  encodeSelectorsAux selectors (List.range groupCount) []

private def minBitsForCount (count : Nat) : Nat :=
  Id.run do
    let mut bits := 0
    while 2 ^ bits < count do
      bits := bits + 1
    pure bits

private def fallbackCodeLengths (alphaSize : Nat) : List Nat :=
  let width := max 1 (minBitsForCount alphaSize)
  let lengths := Array.replicate alphaSize width
  lengths.toList

private def symbolFrequencies (alphaSize : Nat) (symbols : List Nat) : FrequencyTable Nat :=
  let counts :=
    symbols.foldl
      (fun acc symbol =>
        if symbol < alphaSize then
          acc.set! symbol (acc[symbol]! + 1)
        else
          acc)
      (Array.replicate alphaSize 0)
  (List.range alphaSize).map (fun symbol =>
    let freq := counts[symbol]!
    (symbol, if freq = 0 then 1 else freq))

private def tableCodeLengths (alphaSize : Nat) (symbols : List Nat) : Except String (List Nat) := do
  let codec ← Huffman.buildCodec (symbolFrequencies alphaSize symbols)
  let lengths :=
    (Huffman.codeLengths codec).foldl
      (fun acc entry =>
        let symbol := entry.1
        let bitLength := entry.2
        if symbol < alphaSize then
          acc.set! symbol bitLength
        else
          acc)
      (Array.replicate alphaSize 0)
  let lengths := lengths.toList
  if lengths.any (20 < ·) then
    pure (fallbackCodeLengths alphaSize)
  else
    match CanonicalTable.build lengths with
    | .ok _ => pure lengths
    | .error _ => pure (fallbackCodeLengths alphaSize)

private def writeUsedBytes (writer : BitWriter) (usedBytes : List UInt8) : BitWriter :=
  let writer := writer.writeBits 16 (groupsBitmap usedBytes)
  (List.range 16).foldl
    (fun writer group =>
      let mask := groupMask group usedBytes
      if mask = 0 then writer else writer.writeBits 16 mask)
    writer

private def writeUnaryZeroTerminated (writer : BitWriter) (count : Nat) : BitWriter :=
  (writer.writeRepeatedBit count true).writeBit false

private def writeCodeLengthTable (writer : BitWriter) (lengths : List Nat) : BitWriter :=
  Id.run do
    let startLength := lengths.headD 0
    let mut writer := writer.writeBits 5 startLength
    let mut current := startLength
    for target in lengths do
      while current ≠ target do
        writer := writer.writeBit true
        if target < current then
          writer := writer.writeBit true
          current := current - 1
        else
          writer := writer.writeBit false
          current := current + 1
      writer := writer.writeBit false
    pure writer

private def writeSymbolStream
    (writer : BitWriter) (table : CanonicalTable) (symbols : List Nat) :
    Except String BitWriter := do
  symbols.foldlM
    (fun writer symbol => do
      let some entry := table.entries.find? (fun entry => entry.symbol = symbol)
        | throw "Exact `.bz2` encoder generated a symbol missing from the canonical table."
      pure (writer.writeBits entry.bitLength entry.code))
    writer

private def selectorCount (symbols : List Nat) : Nat :=
  max 1 ((symbols.length + 49) / 50)

private def encodeBlock (writer : BitWriter) (block : EntropyInput) : Except String (BitWriter × UInt32) := do
  let blockCRC := crc32 block.original
  let alphaSize := block.usedBytes.length + 2
  -- Compatibility-first exact encoding: emit two valid tables and select the
  -- first one for every 50-symbol group. This matches the wire format cleanly
  -- even though it is not yet tuned for compression ratio.
  let groupCount := 2
  let selectors := List.replicate (selectorCount block.symbols) 0
  let encodedSelectors ← encodeSelectors groupCount selectors
  let tableLengths ← tableCodeLengths alphaSize block.symbols
  let tables := [tableLengths, tableLengths]
  let canonical ← CanonicalTable.build tableLengths
  let writer := writer.writeBits 48 blockMagic
  let writer := writer.writeBits 32 blockCRC.toNat
  let writer := writer.writeBit false
  let writer := writer.writeBits 24 block.origPtr
  let writer := writeUsedBytes writer block.usedBytes
  let writer := writer.writeBits 3 groupCount
  let writer := writer.writeBits 15 selectors.length
  let writer := encodedSelectors.foldl writeUnaryZeroTerminated writer
  let writer := tables.foldl writeCodeLengthTable writer
  let writer ← writeSymbolStream writer canonical block.symbols
  pure (writer, blockCRC)

private def encodeBlocks (writer : BitWriter) (blocks : List EntropyInput) :
    Except String (BitWriter × UInt32) := do
  blocks.foldlM
    (fun (state : BitWriter × UInt32) block => do
      let writer := state.1
      let streamCRC := state.2
      let (writer, blockCRC) ← encodeBlock writer block
      pure (writer, combineStreamCRC streamCRC blockCRC))
    (writer, 0)

private def streamHeaderWriter (config : StreamConfig) : BitWriter :=
  let writer := BitWriter.empty
  let writer := writer.writeBits 8 0x42
  let writer := writer.writeBits 8 0x5A
  let writer := writer.writeBits 8 0x68
  writer.writeBits 8 (48 + config.blockSizeDigit)

/-- Initialize an incremental exact `.bz2` encoder. -/
def StreamEncoderState.init (config : StreamConfig) : StreamEncoderState :=
  { writer := streamHeaderWriter config, streamCRC := 0 }

/--
Append one raw input block to an incremental exact `.bz2` stream.

The raw block is RLE1-encoded and transformed independently, matching the
block-local structure of the exact wire format.
-/
def StreamEncoderState.pushRawBlock?
    (state : StreamEncoderState) (rawBlock : ByteArray) :
    Except String StreamEncoderState := do
  let block : PreparedBlock :=
    { original := rawBlock, rle1 := encodeInitialRLE rawBlock }
  let entropy := prepareEntropyInput block
  let (writer, blockCRC) ← encodeBlock state.writer entropy
  pure
    { writer := writer
    , streamCRC := combineStreamCRC state.streamCRC blockCRC
    }

/-- Finalize an incremental exact `.bz2` stream into bytes. -/
def StreamEncoderState.finish (state : StreamEncoderState) : ByteArray :=
  let writer := state.writer.writeBits 48 endMagic
  let writer := writer.writeBits 32 state.streamCRC.toNat
  writer.toByteArray

/-- Compress bytes into one exact `.bz2` stream using the provided configuration. -/
def compressWithConfig? (config : StreamConfig) (data : ByteArray) : Except String ByteArray := do
  let prepared ← prepareBlocks config.blockSizeBytes data
  let blocks := prepared.map prepareEntropyInput
  let writer := streamHeaderWriter config
  let (writer, streamCRC) ← encodeBlocks writer blocks
  let writer := writer.writeBits 48 endMagic
  let writer := writer.writeBits 32 streamCRC.toNat
  pure writer.toByteArray

/-- Compress bytes into an exact `.bz2` stream using the default `BZh1` configuration. -/
def compress? (data : ByteArray) : Except String ByteArray :=
  compressWithConfig? defaultStreamConfig data

/-- Compress bytes into an exact `.bz2` stream using a `1`-through-`9` block-size digit. -/
def compressWithBlockSize? (blockSizeDigit : Nat) (data : ByteArray) : Except String ByteArray := do
  let config ← streamConfig? blockSizeDigit
  compressWithConfig? config data

end Bzip2.Format.BZ2
