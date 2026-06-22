import Bzip2.Format.BZ2.Encoder
import Bzip2.Format.BZ2.Parser
import Bzip2.Correctness.BZ2.BitsReader
import Bzip2.Correctness.BZ2.UsedBytes

/-!
# Header / marker / padding round trips (B11–B13)

The fixed-width header fields of an exact `.bz2` stream are emitted by the encoder
as `writeBits`/`writeBit` calls and read back by the parser as `readBits`/`readBit`
calls. Each agreement is a direct application of the `BitsReader` bridge
(`readBits_of_prefix` / `readBit_of_prefix`), with the field-value bound
(`value < 2 ^ width`) supplied from the field's domain.

* **B11** — block header after the block magic: 32-bit CRC, 1-bit randomised flag,
  24-bit `origPtr`, then the used-byte bitmap (`parseBlockHeaderAfterMagic`).
* **B12** — stream header `BZh<digit>` and the 48-bit section markers
  (`parseStreamHeader`, `parseSectionMarker`).
* **B13** — the `< 8`-bit zero padding the writer appends at finalize is exactly
  consumed by the reader's `alignToByte`.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

/-! ### B12 — stream header -/

/-- The stream header writer emits `BZh<48+digit>` as four MSB-first bytes. -/
theorem streamHeaderWriter_bits (config : StreamConfig) :
    (streamHeaderWriter config).bits
      = natBitsMSB 8 0x42 ++ natBitsMSB 8 0x5A ++ natBitsMSB 8 0x68
          ++ natBitsMSB 8 (48 + config.blockSizeDigit)
      ∧ (streamHeaderWriter config).WF := by
  rw [streamHeaderWriter]
  have h0 := BitWriter.empty_WF
  have h1 := BitWriter.empty.writeBits_bits h0 8 0x42
  have hw1 := BitWriter.empty.writeBits_WF h0 8 0x42
  have h2 := (BitWriter.empty.writeBits 8 0x42).writeBits_bits hw1 8 0x5A
  have hw2 := (BitWriter.empty.writeBits 8 0x42).writeBits_WF hw1 8 0x5A
  have h3 := ((BitWriter.empty.writeBits 8 0x42).writeBits 8 0x5A).writeBits_bits hw2 8 0x68
  have hw3 := ((BitWriter.empty.writeBits 8 0x42).writeBits 8 0x5A).writeBits_WF hw2 8 0x68
  have h4 := (((BitWriter.empty.writeBits 8 0x42).writeBits 8 0x5A).writeBits 8 0x68).writeBits_bits
    hw3 8 (48 + config.blockSizeDigit)
  have hw4 := (((BitWriter.empty.writeBits 8 0x42).writeBits 8 0x5A).writeBits 8 0x68).writeBits_WF
    hw3 8 (48 + config.blockSizeDigit)
  refine ⟨?_, hw4⟩
  rw [h4, h3, h2, h1]
  simp [BitWriter.bits, BitWriter.empty, List.append_assoc]

/-- Parsing the four header bytes recovers the block-size digit and consumes them. -/
theorem parseStreamHeader_of_prefix (reader : BitReader) (d : Nat) (rest : List Bool)
    (hd : 1 ≤ d ∧ d ≤ 9)
    (hpre : (bitListOf reader.bytes).drop reader.bitPos
      = natBitsMSB 8 0x42 ++ natBitsMSB 8 0x5A ++ natBitsMSB 8 0x68 ++ natBitsMSB 8 (48 + d) ++ rest) :
    ∃ reader', parseStreamHeader reader
        = .ok ({ blockSizeDigit := d, blockSizeBytes := d * 100000 }, reader')
      ∧ reader'.bytes = reader.bytes
      ∧ (bitListOf reader'.bytes).drop reader'.bitPos = rest := by
  -- regroup the prefix so each field is a leading `natBitsMSB 8 _`
  rw [List.append_assoc, List.append_assoc, List.append_assoc] at hpre
  obtain ⟨hr1, hrem1⟩ := readBits_of_prefix reader 8 0x42 _ (by decide) hpre
  obtain ⟨hr2, hrem2⟩ :=
    readBits_of_prefix { reader with bitPos := reader.bitPos + 8 } 8 0x5A _ (by decide) (by simpa using hrem1)
  obtain ⟨hr3, hrem3⟩ :=
    readBits_of_prefix { reader with bitPos := reader.bitPos + 8 + 8 } 8 0x68 _ (by decide)
      (by simpa using hrem2)
  obtain ⟨hr4, hrem4⟩ :=
    readBits_of_prefix { reader with bitPos := reader.bitPos + 8 + 8 + 8 } 8 (48 + d) _
      (by rw [show (2:Nat) ^ 8 = 256 from by decide]; omega) (by simpa using hrem3)
  refine ⟨{ reader with bitPos := reader.bitPos + 8 + 8 + 8 + 8 }, ?_, rfl, by simpa using hrem4⟩
  rw [parseStreamHeader]
  simp only [hr1, hr2, hr3, hr4, bind, Except.bind, pure, Except.pure]
  rw [if_neg (by decide : ¬ ((0x42 : Nat) ≠ 0x42 ∨ (0x5A : Nat) ≠ 0x5A ∨ (0x68 : Nat) ≠ 0x68)),
    if_pos (by omega : 49 ≤ 48 + d ∧ 48 + d ≤ 57)]
  have : 48 + d - 48 = d := by omega
  rw [this]

/-- Stream-header writer/parser agreement: parsing what `streamHeaderWriter`
emits recovers the same block-size digit. -/
theorem parseStreamHeader_streamHeaderWriter (config : StreamConfig) (reader : BitReader)
    (rest : List Bool) (hd : 1 ≤ config.blockSizeDigit ∧ config.blockSizeDigit ≤ 9)
    (hpre : (bitListOf reader.bytes).drop reader.bitPos
      = (streamHeaderWriter config).bits ++ rest) :
    ∃ reader', parseStreamHeader reader
        = .ok ({ blockSizeDigit := config.blockSizeDigit
               , blockSizeBytes := config.blockSizeDigit * 100000 }, reader')
      ∧ reader'.bytes = reader.bytes
      ∧ (bitListOf reader'.bytes).drop reader'.bitPos = rest := by
  rw [(streamHeaderWriter_bits config).1] at hpre
  simp only [List.append_assoc] at hpre
  exact parseStreamHeader_of_prefix reader config.blockSizeDigit rest hd (by simpa [List.append_assoc] using hpre)

/-! ### B12 — section markers -/

/-- The 48-bit block magic parses to a `.block` marker. -/
theorem parseSectionMarker_block_of_prefix (reader : BitReader) (rest : List Bool)
    (hpre : (bitListOf reader.bytes).drop reader.bitPos = natBitsMSB 48 blockMagic ++ rest) :
    ∃ reader', parseSectionMarker reader = .ok (.block, reader')
      ∧ reader'.bytes = reader.bytes
      ∧ (bitListOf reader'.bytes).drop reader'.bitPos = rest := by
  obtain ⟨hr, hrem⟩ := readBits_of_prefix reader 48 blockMagic rest (by decide) hpre
  refine ⟨{ reader with bitPos := reader.bitPos + 48 }, ?_, rfl, by simpa using hrem⟩
  rw [parseSectionMarker]
  simp only [hr, bind, Except.bind, pure, Except.pure, if_true]

/-- The 48-bit end magic parses to an `.eos` marker. -/
theorem parseSectionMarker_eos_of_prefix (reader : BitReader) (rest : List Bool)
    (hpre : (bitListOf reader.bytes).drop reader.bitPos = natBitsMSB 48 endMagic ++ rest) :
    ∃ reader', parseSectionMarker reader = .ok (.eos, reader')
      ∧ reader'.bytes = reader.bytes
      ∧ (bitListOf reader'.bytes).drop reader'.bitPos = rest := by
  obtain ⟨hr, hrem⟩ := readBits_of_prefix reader 48 endMagic rest (by decide) hpre
  refine ⟨{ reader with bitPos := reader.bitPos + 48 }, ?_, rfl, by simpa using hrem⟩
  rw [parseSectionMarker]
  simp only [hr, bind, Except.bind, pure, Except.pure,
    if_neg (by decide : ¬ (endMagic = blockMagic)), if_true]

/-! ### B11 — block header after the magic -/

/-- Block-header agreement: a 32-bit CRC, the 1-bit randomised flag, a 24-bit
`origPtr`, and the used-byte bitmap parse back to the same `BlockHeader`. -/
theorem parseBlockHeaderAfterMagic_of_prefix
    (reader : BitReader) (crc origPtr : Nat) (us : List UInt8) (rest : List Bool)
    (hcrc : crc < 2 ^ 32) (hptr : origPtr < 2 ^ 24)
    (hs : us.Pairwise (· ≤ ·)) (hn : us.Nodup)
    (hpre : (bitListOf reader.bytes).drop reader.bitPos
      = natBitsMSB 32 crc ++ [false] ++ natBitsMSB 24 origPtr
          ++ (natBitsMSB 16 (groupsBitmap us) ++ maskBits us) ++ rest) :
    ∃ reader', parseBlockHeaderAfterMagic reader
        = .ok ({ blockCRC := UInt32.ofNat crc, randomised := false
               , origPtr := origPtr, usedBytes := us }, reader')
      ∧ reader'.bytes = reader.bytes
      ∧ (bitListOf reader'.bytes).drop reader'.bitPos = rest := by
  rw [List.append_assoc, List.append_assoc, List.append_assoc] at hpre
  obtain ⟨hr1, hrem1⟩ := readBits_of_prefix reader 32 crc _ hcrc hpre
  obtain ⟨hr2, hrem2⟩ :=
    readBit_of_prefix { reader with bitPos := reader.bitPos + 32 } false _ (by simpa using hrem1)
  obtain ⟨hr3, hrem3⟩ :=
    readBits_of_prefix { reader with bitPos := reader.bitPos + 32 + 1 } 24 origPtr _ hptr
      (by simpa using hrem2)
  obtain ⟨reader', hr4, hb4, hrem4⟩ :=
    parseUsedBytes_roundtrip us hs hn { reader with bitPos := reader.bitPos + 32 + 1 + 24 }
      rest (by simpa [List.append_assoc] using hrem3)
  refine ⟨reader', ?_, by rw [hb4], hrem4⟩
  rw [parseBlockHeaderAfterMagic]
  simp only [hr1, hr2, hr3, bind, Except.bind, pure, Except.pure]
  rw [hr4]

/-! ### B13 — finalize padding -/

/-- The reader's `alignToByte` consumes exactly the `< 8`-bit zero padding the
writer appends at finalize: if the remaining bits are precisely the padding to the
next byte boundary, after aligning nothing remains. -/
theorem alignToByte_consumes_padding (r : BitReader)
    (hrem : (bitListOf r.bytes).drop r.bitPos = List.replicate ((8 - r.bitPos % 8) % 8) false) :
    (bitListOf r.alignToByte.bytes).drop r.alignToByte.bitPos = [] := by
  by_cases hal : r.bitPos % 8 = 0
  · have : (8 - r.bitPos % 8) % 8 = 0 := by omega
    rw [BitReader.alignToByte, show r.isByteAligned = true by simp [BitReader.isByteAligned, hal]]
    simp only [if_true]
    rw [this, List.replicate_zero] at hrem
    exact hrem
  · have hpos : 0 < r.bitPos % 8 := by omega
    have hlt : r.bitPos % 8 < 8 := Nat.mod_lt _ (by decide)
    have hpad : (8 - r.bitPos % 8) % 8 = 8 - r.bitPos % 8 := by omega
    rw [BitReader.alignToByte,
      show r.isByteAligned = false by simp [BitReader.isByteAligned, hal]]
    simp only [Bool.false_eq_true, if_false]
    show (bitListOf r.bytes).drop (r.bitPos + (8 - r.bitPos % 8)) = []
    rw [← List.drop_drop, hrem, hpad, List.drop_replicate]
    simp

end Bzip2.Format.BZ2
