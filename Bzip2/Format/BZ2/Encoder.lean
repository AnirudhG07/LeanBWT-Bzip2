import Bzip2.Format.BZ2.BitWriter
import Bzip2.Format.BZ2.CRC
import Bzip2.Format.BZ2.Canonical
import Bzip2.Format.BZ2.InverseBWT
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

/-- Least `bits` with `count ≤ 2 ^ bits`; the ceiling base-2 logarithm. -/
private def minBitsForCount (count : Nat) : Nat :=
  Nat.clog 2 count

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

/-- Emit the unary delta steps that move the running code length to `target`. -/
private def writeLengthDelta (writer : BitWriter) (current target : Nat) : BitWriter :=
  if current = target then
    writer
  else if target < current then
    writeLengthDelta ((writer.writeBit true).writeBit true) (current - 1) target
  else
    writeLengthDelta ((writer.writeBit true).writeBit false) (current + 1) target
termination_by (current - target) + (target - current)
decreasing_by all_goals omega

private def writeCodeLengthTableAux (current : Nat) :
    List Nat → BitWriter → BitWriter
  | [], writer => writer
  | target :: rest, writer =>
      let writer := writeLengthDelta writer current target
      writeCodeLengthTableAux target rest (writer.writeBit false)

private def writeCodeLengthTable (writer : BitWriter) (lengths : List Nat) : BitWriter :=
  let startLength := lengths.headD 0
  writeCodeLengthTableAux startLength lengths (writer.writeBits 5 startLength)

/-- Number of 50-symbol groups (and thus selectors) for one block. -/
def selectorCount (symbols : List Nat) : Nat :=
  max 1 ((symbols.length + 49) / 50)

/-- Huffman group count by MTF symbol count, matching bzip2's `sendMTFValues`. -/
def nGroupsForSymbolCount (count : Nat) : Nat :=
  if count < 200 then 2
  else if count < 600 then 3
  else if count < 1200 then 4
  else if count < 2400 then 5
  else 6

/-- Per-block entropy-coding plan: code-length tables plus one selector per group. -/
structure EntropyPlan where
  tables : List (List Nat)
  selectors : List Nat
deriving Repr

/--
Validity contract between the planner and the wire emitter. `encodeBlock`
re-checks this dynamically, so correctness of emitted streams never depends
on how the planner chose the plan.
-/
def EntropyPlan.valid (plan : EntropyPlan) (alphaSize symbolCount : Nat) : Bool :=
  2 ≤ plan.tables.length
    && plan.tables.length ≤ 6
    && plan.tables.all (fun lengths => lengths.length = alphaSize)
    && plan.selectors.length = max 1 ((symbolCount + 49) / 50)
    && plan.selectors.length < 32768
    && plan.selectors.all (· < plan.tables.length)

private def rawFrequencies (alphaSize : Nat) (symbols : List Nat) : Array Nat :=
  symbols.foldl
    (fun acc symbol =>
      if symbol < alphaSize then
        acc.set! symbol (acc[symbol]! + 1)
      else
        acc)
    (Array.replicate alphaSize 0)

/--
Initial cost tables seeding the refinement iterations: partition the alphabet
into `nGroups` contiguous ranges of roughly equal total frequency, scoring
in-range symbols as cheap (0) and out-of-range symbols as expensive (15).
These seeds are never emitted; refinement replaces them with real lengths.
-/
private def initialCostTables (alphaSize nGroups : Nat) (freq : Array Nat) :
    Array (Array Nat) :=
  Id.run do
    let total := freq.foldl (· + ·) 0
    let mut tables : Array (Array Nat) := #[]
    let mut gs := 0
    let mut remF := total
    let mut nPart := nGroups
    while nPart > 0 do
      let target := remF / nPart
      let mut ge := gs
      let mut aFreq := 0
      while (aFreq < target ∨ ge = gs) && ge < alphaSize do
        aFreq := aFreq + freq[ge]!
        ge := ge + 1
      let hi := if nPart = 1 then alphaSize else ge
      let lengths := Array.ofFn (n := alphaSize)
        (fun s => if gs ≤ s.val && s.val < hi then 0 else 15)
      tables := tables.push lengths
      remF := remF - aFreq
      gs := hi
      nPart := nPart - 1
    pure tables

private def chunksOf50 (symbols : Array Nat) : Array (Array Nat) :=
  Id.run do
    let mut chunks : Array (Array Nat) := #[]
    let mut index := 0
    while index < symbols.size do
      chunks := chunks.push (symbols.extract index (index + 50))
      index := index + 50
    pure chunks

private def groupCost (lengths : Array Nat) (chunk : Array Nat) : Nat :=
  chunk.foldl (fun acc symbol => acc + lengths.getD symbol 15) 0

private def cheapestTable (tables : Array (Array Nat)) (chunk : Array Nat) : Nat :=
  Id.run do
    let mut best := 0
    let mut bestCost := groupCost (tables.getD 0 #[]) chunk
    for t in [1:tables.size] do
      let cost := groupCost tables[t]! chunk
      if cost < bestCost then
        best := t
        bestCost := cost
    pure best

/--
One refinement pass: assign every 50-symbol group to its cheapest table, then
rebuild each table's code lengths from the symbols it was assigned.
-/
private def refineOnce (alphaSize : Nat) (chunks : Array (Array Nat))
    (tables : Array (Array Nat)) :
    Except String (Array Nat × Array (Array Nat)) := do
  let selectors := chunks.map (cheapestTable tables)
  let mut assigned : Array (List Nat) := Array.replicate tables.size []
  for h : i in [0:chunks.size] do
    let t := selectors[i]!
    assigned := assigned.set! t (chunks[i].toList ++ assigned[t]!)
  let mut rebuilt : Array (Array Nat) := #[]
  for syms in assigned do
    let lengths ← tableCodeLengths alphaSize syms
    rebuilt := rebuilt.push lengths.toArray
  pure (selectors, rebuilt)

/--
Choose the per-block Huffman tables and selectors, mirroring the structure of
bzip2's `sendMTFValues`: 2-6 tables by symbol count, frequency-partitioned
seeds, then four greedy refinement iterations.
-/
def planEntropyCoding (alphaSize : Nat) (symbols : List Nat) :
    Except String EntropyPlan := do
  let nGroups := nGroupsForSymbolCount symbols.length
  let chunks := chunksOf50 symbols.toArray
  let freq := rawFrequencies alphaSize symbols
  let mut tables := initialCostTables alphaSize nGroups freq
  let mut selectors : Array Nat := Array.replicate (max 1 chunks.size) 0
  for _ in [0:4] do
    let (selectors', tables') ← refineOnce alphaSize chunks tables
    selectors := if selectors'.isEmpty then selectors else selectors'
    tables := tables'
  pure { tables := tables.toList.map (·.toList), selectors := selectors.toList }

private def codeLookup (alphaSize : Nat) (table : CanonicalTable) : Array (Nat × Nat) :=
  table.entries.foldl
    (fun acc entry =>
      if entry.symbol < alphaSize then
        acc.set! entry.symbol (entry.bitLength, entry.code)
      else
        acc)
    (Array.replicate alphaSize (0, 0))

private def writeSymbolsAux
    (lookups : Array (Array (Nat × Nat))) (selectors : Array Nat) :
    List Nat → Nat → BitWriter → Except String BitWriter
  | [], _, writer => pure writer
  | symbol :: rest, count, writer => do
      let some selector := selectors[count / 50]?
        | throw "Exact `.bz2` encoder ran out of Huffman selectors."
      let some lookup := lookups[selector]?
        | throw "Exact `.bz2` encoder selector references a missing Huffman table."
      let some (bitLength, code) := lookup[symbol]?
        | throw "Exact `.bz2` encoder generated a symbol missing from the canonical table."
      if bitLength = 0 then
        throw "Exact `.bz2` encoder selected a table without a code for a symbol."
      writeSymbolsAux lookups selectors rest (count + 1) (writer.writeBits bitLength code)

private def writeSymbolStream
    (writer : BitWriter) (lookups : Array (Array (Nat × Nat))) (selectors : List Nat)
    (symbols : List Nat) : Except String BitWriter :=
  writeSymbolsAux lookups selectors.toArray symbols 0 writer

private def encodeBlock (writer : BitWriter) (block : EntropyInput) : Except String (BitWriter × UInt32) := do
  let blockCRC := crc32 block.original
  -- BWT self-check: confirm the decoder's inverse BWT reproduces this block's
  -- pre-BWT bytes. This makes stream correctness independent of which forward
  -- BWT was used: a faulty transform can only fail compression here, never
  -- emit a stream that decodes to the wrong bytes.
  match inverseBWT block.lastColumn block.origPtr with
  | .error err =>
      throw s!"Exact `.bz2` encoder BWT self-check failed: {err}"
  | .ok recovered =>
      if recovered != block.rle1 then
        throw "Exact `.bz2` encoder BWT self-check failed: inverse did not reproduce the block."
  let alphaSize := block.usedBytes.length + 2
  let plan ← planEntropyCoding alphaSize block.symbols
  if !plan.valid alphaSize block.symbols.length then
    throw "Exact `.bz2` encoder produced an invalid entropy-coding plan."
  let groupCount := plan.tables.length
  let selectors := plan.selectors
  let encodedSelectors ← encodeSelectors groupCount selectors
  let canonicals ← plan.tables.mapM CanonicalTable.build
  let lookups := (canonicals.map (codeLookup alphaSize)).toArray
  let writer := writer.writeBits 48 blockMagic
  let writer := writer.writeBits 32 blockCRC.toNat
  let writer := writer.writeBit false
  let writer := writer.writeBits 24 block.origPtr
  let writer := writeUsedBytes writer block.usedBytes
  let writer := writer.writeBits 3 groupCount
  let writer := writer.writeBits 15 selectors.length
  let writer := encodedSelectors.foldl writeUnaryZeroTerminated writer
  let writer := plan.tables.foldl writeCodeLengthTable writer
  let writer ← writeSymbolStream writer lookups selectors block.symbols
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
