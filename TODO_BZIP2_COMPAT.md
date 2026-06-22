# TODO: Real `.bz2` Compatibility and Correctness Roadmap

This document is the project plan from the current verified BWT-based prototype
to a real implementation that can interoperate with the Linux `bzip2` /
`bunzip2` tools and come with correctness proofs for the newer implementation.

## End Goal

We want all of the following to be true:

- Our decoder can read `.bz2` files produced by the system `bzip2`.
- Our encoder can produce `.bz2` files that the system `bzip2` can test and
  decompress.
- Small, medium, and large file tests all pass for text and binary inputs.
- The new implementation is proved correct by refinement from the existing BWT
  basics and abstract correctness results.

## Definition of Done — Master Checklist

This is the single authoritative list. **The project is REALLY done — industry
support, the industry implementation proved correct, everything — exactly when
every box A1–F8 below is checked.** Each item is either done (`[x]`), or pending
(`[ ]`) with the responsible proof/engineering phase noted. Nothing outside this
list is required; nothing inside it may be skipped.

### A. Industry-standard implementation & interoperability

- [x] **A1.** Exact `.bz2` wire format: `BZh` stream header, 48-bit block /
  end-of-stream magics, per-block CRC32 and combined stream CRC32, initial RLE1,
  BWT + `origPtr`, MTF, RUNA/RUNB with end-of-block symbol, 16×16 used-byte
  bitmap, 2–6 canonical Huffman tables, per-50-symbol selectors, exact MSB-first
  bit packing.
- [x] **A2.** Encoder output is validated (`bzip2 -t`) and decompressed by system
  `bzip2`, byte-identical to the input.
- [x] **A3.** Decoder reads system-`bzip2`-produced `.bz2` byte-identically.
- [x] **A4.** Real multi-table Huffman encoder (2–6 tables, iterative
  refinement) — competitive ratio vs system bzip2 (bench).
- [x] **A5.** `bzip2`-compatible CLI: clustered flags, `-1..-9`, `-d/-z/-t/-k/-c/
  -f/-q/-v/-s/-L/-V/--help/--`, exit codes 0/1/2/3, `bunzip2`/`bzcat` aliasing,
  stdin/stdout filtering, suffix rules, permission copying.
- [x] **A6.** Interop across block sizes 1–9, text and binary, concatenated
  streams, corruption rejection, full 256-byte alphabet — all in the test suite.
- [x] **A7.** Test driver + CI test execution + CLI smoke matrix + benchmark
  script.
- [ ] **A8.** Streaming / bounded memory: `BitWriter` backed by `ByteArray` with
  a `drain`, handle-backed `BitSource` refilling in chunks, so encoder *and*
  decoder memory stays ≈ one block independent of file size. (Phase A5 / 6.)
- [ ] **A9.** Fast canonical Huffman decode via bzip2-style limit/base/perm
  arrays; accumulator `ByteArray`s on hot decode paths. (Phase A5.)
- [ ] **A10.** Opt-in large-file suite (`LEANBZIP2_RUN_LARGE=1`) green on
  multi-megabyte inputs after A8.

### B. Correctness — exact-format component round trips (bit-accurate)

- [x] **B1.** Bit-writer denotation: `writeBit`/`writeBits`/`writeRepeatedBit`
  append exactly the expected bits, with a preserved `WF` invariant.
- [x] **B2.** Bit-reader positional denotation over `bitListOf`: `readBit_eq`,
  `readBits_eq`, `readBits_of_prefix`, `readBit_of_prefix`.
- [x] **B3.** Writer finalization bridge: `bitListOf (toByteArray w) = w.bits ++
  padding`; fresh-reader entry point.
- [x] **B4.** Initial RLE1 round trip (`decodeInitialRLE ∘ encodeInitialRLE`).
- [x] **B5.** RUNA/RUNB zero-run digit round trip.
- [x] **B6.** MTF + RUNA/RUNB payload round trip (last column ↔ symbol stream).
- [x] **B7.** Selector move-to-front round trip (index level).
- [x] **B8.** Selector unary bit coding round trip
  (`writeUnaryZeroTerminated` ↔ `parseUnaryIndex`), composed with B7 to give the
  full on-the-wire selector round trip.
  - `Bzip2/Correctness/BZ2/SelectorBits.lean`, headline `parseSelectors_roundtrip`:
    `parseUnaryIndexAux_of_prefix` (unary core via the bridge),
    `parseSelectorsAux_of_prefix` (the parser's unary-read + move-to-front decode
    matches `decodeSelectorsAux`), `encodeSelectorsAux_lt` (encoded indices are
    valid group indices), composed with B7's `decodeSelectors_encodeSelectors`.
- [x] **B9.** Huffman code-length delta-table round trip (5-bit start + per-symbol
  unary delta walk).
- [x] **B10.** Used-byte 16×16 bitmap round trip for a sorted-nodup alphabet.
  - `Bzip2/Correctness/BZ2/UsedBytes.lean`, headline `parseUsedBytes_roundtrip`.
  - Combinatorial heart: `testBit_add_of_disjoint` (disjoint add = bitwise-or),
    `testBit_sum_two_pow` (a bit of a sum of distinct powers recovers
    membership), and the mask characterizations `groupMask_bit` /
    `groupsBitmap_bit`, plus 16-bit bounds.
  - Parser side: `parseUsedBytesAux_spec` threads `writeUsedBytes`'s bits through
    the 16 interleaved 16-bit mask reads via the `BitsReader` bridge, yielding the
    per-group reconstruction; `reconstruct_eq` then shows the concatenated
    per-group bytes equal the alphabet (a sorted-nodup list = the ascending byte
    enumeration filtered by membership, via `sorted_nodup_ext`). `usedBytes` is
    proved ascending + nodup (`usedBytes_pairwise`/`usedBytes_nodup`).
- [x] **B11.** Block-header field serialize/parse agreement (`Headers.lean`,
  `parseBlockHeaderAfterMagic_of_prefix`): blockCRC (32), `randomised`=0 (1),
  `origPtr` (24), then the used-byte bitmap (composes `parseUsedBytes_roundtrip`).
  Each fixed field is a direct `readBits_of_prefix`/`readBit_of_prefix`
  application with the field-domain bound. (The Huffman group count (3) and
  selector count (15) live at the head of `parseHuffmanMetadata` and are read by
  the same `readBits_of_prefix` recipe; they fold into the B4 block assembly.)
- [x] **B12.** Stream header (`BZh`+digit) and 48-bit section markers
  serialize/parse agreement (`Headers.lean`): `streamHeaderWriter_bits` +
  `parseStreamHeader_of_prefix`/`parseStreamHeader_streamHeaderWriter` (recovers
  the 1–9 block-size digit), and `parseSectionMarker_block_of_prefix` /
  `parseSectionMarker_eos_of_prefix` (block vs end magic, distinguished by
  `blockMagic ≠ endMagic`).
- [x] **B13.** Byte-alignment padding (`Headers.lean`,
  `alignToByte_consumes_padding`): if the remaining bits are exactly the padding
  to the next byte boundary (the `<8`-bit zero tail `bitListOf_toByteArray`
  appends at finalize), the reader's `alignToByte` consumes them and nothing
  remains.

### C. Canonical Huffman (Phase 5 / B3)

- [ ] **C1.** Build spec as an inductive predicate (one entry per positive length,
  consecutive codes, `firstCode(l+1) = 2·(firstCode(l)+count(l))`).
- [ ] **C2.** Prefix-freeness from the interval invariant + not-overfull check.
- [ ] **C3.** `decodeSymbol` correctness: `decode ∘ encode = id` per symbol
  (fuel-induction, prefix-freeness kills early hits).
- [ ] **C4.** `fallbackCodeLengths` always builds successfully.
- [ ] **C5.** Trust boundary resolved: state explicitly that every property the
  headline needs (build succeeded, all symbols have entries, lengths ≤ 20) is
  dynamically checked on the encoder's `.ok` path — so the conditional headline
  theorem needs **zero** facts about `LeanHuffmanCoding` — **or** internalize a
  proved Huffman builder.

### D. Block & stream assembly — the headline theorem (Phase 5 / B4–B5)

- [ ] **D1.** Per-block agreement: decoding `encodeBlock block` recovers the block
  (stitch B6–B13 + C3 per-symbol decode + selector/group bookkeeping for the
  multi-table planner).
- [ ] **D2.** Block CRC: the decoder's recomputed CRC32 equals the emitted one, so
  a correctly-encoded block is never rejected (CRC determinism).
- [ ] **D3.** **Headline round-trip theorem:**
  `compress? data = .ok out → decompress? out = .ok data`.
- [ ] **D4.** Generalizations: `compressWithBlockSize?` and `compressWithConfig?`
  (every valid block size / entropy plan).
- [ ] **D5.** Edge cases inside D3: empty input, single block, multi-block, the
  end-of-stream marker, the trailing stream CRC, and padding consumption.

### E. BWT refinement proofs (Phase 5.3 / B6–B7)

- [ ] **E1.** Reference BWT inversion:
  `inverseBWT (transformBWTReference x).lastColumn origPtr = .ok x`, proved in the
  `origPtr`/cyclic formalism.
- [ ] **E2.** Fast BWT refines reference: `transformFastBWT = transformBWTReference`.
- [ ] **E3.** Fast inverse BWT agrees with the reference inverse where they
  overlap (or is shown equal to the proved `inverseBWT`).
- [ ] **E4.** Once E1–E3 land, the runtime BWT self-check in `encodeBlock` is
  provably redundant; decide to keep it (defensive) or remove it, and record that
  the headline no longer depends on it.

### F. Trust, hygiene, finalization

- [x] **F1.** Zero `sorry`/`admit` anywhere in `Bzip2/`.
- [ ] **F2.** No `partial def` on any proof-relevant path. (Currently only two
  IO-sink `partial def`s remain in `Decoder.lean`, off the pure proof path — keep
  documented, or de-partialize.)
- [ ] **F3.** `#print axioms` on the headline theorem (D3) shows no axioms beyond
  the standard mathlib/Lean core set (no `sorryAx`, no project-specific axioms).
- [ ] **F4.** Every `private` removed to enable proofs is either re-`private`d
  behind a stable proof-facing interface or documented as public API.
- [ ] **F5.** CI: builds the whole project, runs all test suites, and fails on any
  `sorry` or build warning regression.
- [ ] **F6.** README + this TODO reflect the final state; compatibility matrix and
  proof-status table accurate.
- [ ] **F7.** (Stretch, optional for "done") Decoder soundness for *arbitrary*
  valid input: any stream system `bzip2` accepts, our `decompress?` decodes
  identically — strictly stronger than the round trip; explicitly in- or
  out-of-scope decided and recorded.
- [ ] **F8.** Final sign-off: a single aggregated theorem (or documented theorem
  list) that, taken together, states "this exact `.bz2` codec is correct," with a
  one-paragraph English statement of exactly what is and isn't guaranteed.

---

**Progress at a glance:** A1–A7 ✓, A8–A10 pending · B1–B13 ✓ · C pending ·
D pending · E pending · F1 ✓, F2–F8 pending. The implementation and interop are
essentially complete, and the entire per-component bit-accurate round-trip layer
(B1–B13: bit IO, RLE1, RUNA/RUNB, MTF, selectors, used-byte map, code-length
tables, headers, markers, padding) is now proved. The bulk of remaining work is
the proof stack **C** (canonical Huffman build + decode correctness) and **D**
(the headline `compress? data = .ok out → decompress? out = .ok data`, which
stitches B1–B13 + C together), then the BWT refinement proofs **E**, then
finalization **F**.

> Dependency note (2026-06-13): the upstream `huffman` library
> (`github.com/AnirudhG07/LeanHuffmanCoding`) was bumped to rev `5dc175f`
> ("codec correctness"), which now ships `decodeBits_encodeSymbols` (a full codec
> round-trip) in its `HuffmanProofs` lib. Same toolchain/mathlib as ours; build +
> all interop suites green after the bump. We still only consume `Huffman.Codec`
> (code-length assignment for the .bz2 path is trusted-for-quality-only — see C/B3).

## Current State

- [x] Abstract BWT, inverse BWT, MTF, and RLE pipeline proved correct.
- [x] The original BWT construction remains the proved semantic reference.
- [x] A separate fast runtime forward BWT now exists for the exact `.bz2`
  encoder path.
- [x] ByteArray-facing API exists.
- [x] Block-oriented `BZh`-style outer stream exists.
- [x] Per-block CRC and combined stream CRC exist.
- [x] bz2-like block payload now contains:
  - [x] `randomised = 0`
  - [x] `origPtr`
  - [x] used-byte symbol map
  - [x] MTF/RLE payload entries
- [x] Cross-stream behaviors already tested locally:
  - [x] single-block roundtrip
  - [x] multi-block roundtrip
  - [x] concatenated-stream roundtrip
  - [x] corruption rejection
  - [x] full 256-byte alphabet roundtrip

## BWT Strategy Going Forward

We are **not** replacing the original proved BWT development.

Instead, the project will keep two BWT layers side by side:

- `Reference BWT`
  - the current rotation-based construction
  - proof-oriented
  - retained as the mathematical specification and correctness anchor
- `Native / Fast BWT`
  - a new practical block-sorting implementation
  - array/index based rather than rotation-matrix based
  - used by the executable compressor/decompressor for real workloads

The plan is to prove that the fast native BWT refines the original proved BWT,
not to delete or rewrite the original proof development.

## Main Gap

**Status (updated):** the exact `.bz2` block coding is fully implemented and
interoperates with system `bzip2`/`bunzip2` both directions (verified by the test
suite across block sizes 1–9, text/binary, concatenated streams, and corruption
rejection). The following are all DONE on the implementation side:

- initial RLE1 before BWT
- post-MTF RUNA/RUNB encoding
- end-of-block symbol
- 2 to 6 Huffman tables (multi-table entropy planner)
- selector list for groups of 50 symbols
- canonical Huffman code-length encoding
- exact bit-level packing
- a bzip2-compatible CLI (`lake exe bzip2`, with `bunzip2`/`bzcat` aliasing)

The remaining work is entirely on the **proof** side: completing the exact-layer
correctness proofs (Phase 5) up to the headline round-trip theorem, plus the two
BWT refinement proofs. See Phase 5 below for the live checklist.

## Original Recommended Order (historical)

1. Exact decoder for real `.bz2` blocks. — done
2. Exact encoder for real `.bz2` blocks. — done
3. Fast native BWT / inverse-BWT implementation for practical execution. — done
   (runtime-validated by the encoder BWT self-check; refinement proof pending)
4. Refinement proofs from abstract pipeline to real implementation. — in progress
   (Phase 5)
5. Large interoperability and regression test suite. — done

## Phase 0: Freeze and Clean Boundaries

- [x] Freeze the current verified abstract layer as the semantic spec.
- [x] Write down the trust boundary for external dependencies.
  - `LeanHuffmanCoding` is now treated as a proved external dependency for the
    native/format layer.
- [x] Separate modules clearly:
  - `Spec`: proved abstract BWT/MTF/RLE semantics
  - `Format`: exact `.bz2` bitstream structures
  - `Native`: executable encoder/decoder
  - `Correctness`: refinement theorems
- [x] Update README and public docs to distinguish:
  - abstract / bz2-like
  - exact `.bz2` compatible

## Phase 1: Exact `.bz2` Block Decoder

Goal: decode real Linux-generated `.bz2` files.

- [x] Add a real bit reader.
  - read 1 bit
  - read `n` bits
  - byte alignment helpers
  - EOF/error handling
- [x] Parse exact stream header:
  - `BZh`
  - block-size digit `1` to `9`
- [x] Parse exact block header:
  - block magic
  - block CRC
  - randomised flag
  - `origPtr`
  - used-byte map
- [x] Parse Huffman metadata:
  - number of Huffman groups
  - selector count
  - selector MTF list
  - code-length deltas
- [x] Build canonical Huffman decode tables from parsed lengths.
- [x] Decode Huffman-coded symbol stream.
- [x] Decode RUNA/RUNB into MTF positions.
- [x] Stop at the exact end-of-block symbol.
- [x] Invert MTF using the used-byte alphabet.
- [x] Invert BWT using `origPtr`.
- [x] Add initial-RLE1 decode after inverse BWT.
- [x] Decode concatenated `.bz2` streams.
- [x] Reject invalid CRCs and malformed streams with good errors.

## Phase 2: Exact `.bz2` Block Encoder

Goal: emit `.bz2` files accepted by system `bzip2`.

- [x] Add initial RLE1 encode before BWT.
- [x] Run BWT on the RLE1 block data.
- [x] Emit exact `origPtr`.
- [x] Build used-byte symbol map from the block alphabet.
- [x] Run MTF over the used-byte alphabet.
- [x] Encode zero runs using RUNA/RUNB.
- [x] Append exact end-of-block symbol.
- [x] Split symbol stream into groups of 50.
- [x] Choose 2 to 6 Huffman tables.
- [x] Compute selector list.
- [x] MTF-encode selectors.
- [x] Emit canonical code lengths with the exact delta encoding.
- [x] Bit-pack exact block contents without custom byte padding mistakes.
- [x] Emit exact end-of-stream marker and combined CRC.

## Phase 3: Linux Interoperability Milestones

These are the concrete gates for “real compatibility”.

- [x] `bzip2 -dc system_file.bz2` == our decoder output.
- [x] `our_compress file | bzip2 -dc` reproduces the original bytes.
- [x] `bzip2 -t our_output.bz2` succeeds.
- [x] `bunzip2` can decompress our output files without complaint.
- [x] Concatenated streams work both ways when practical.
- [x] Mixed test corpus passes for all block sizes `-1` through `-9`.

## Phase 4: Test Suite Expansion

Checkboxes in this phase mean a runnable case is present in the current test
harness. Cases left unchecked are still planned, but not yet honest to run on
the current implementation.

### Small deterministic cases

- [x] empty file
- [x] one byte
- [x] two bytes
- [x] three bytes
- [x] four equal bytes
- [x] five equal bytes
- [x] alternating bytes
- [x] all 256 byte values once
- [x] all 256 byte values repeated

### Medium files

- [x] short English text
- [x] source code
- [x] JSON
- [x] repetitive binary
- [x] pseudo-random binary
- [x] data crossing one block boundary

### Large files

- [x] multi-megabyte text
- [x] multi-megabyte binary
- [x] highly repetitive large file
- [x] incompressible large file
- [x] files spanning many blocks

Notes:
- The opt-in large harness now passes a 1 GiB shell baseline on a sparse file.
- The same harness also passes exact sparse interop on the default 16 MiB
  multi-block exact setting, plus multi-megabyte text/binary, incompressible
  large-file, and many-block shell cases.

### Negative / robustness tests

- [x] bad magic
- [x] bad block CRC
- [x] bad stream CRC
- [x] malformed selector list
- [x] malformed code lengths
- [x] missing end-of-block symbol
- [x] truncated stream
- [x] trailing garbage
- [x] concatenated stream with second stream damaged

## Phase 5: Proof Plan

Goal: prove the newer exact implementation correct from the BWT basics upward.

### 5.1 Semantic layering

- [x] Introduce a separate fast native BWT layer without deleting the existing
  proved BWT construction.
- [x] Decouple stream correctness from forward-BWT correctness via a runtime
  self-check: `encodeBlock` now verifies `inverseBWT lastColumn origPtr = rle1`
  and fails compression otherwise, so a faulty forward BWT can never produce a
  stream that decodes to the wrong bytes. This lets the BWT refinement proofs
  (5.3) be deferred without weakening the headline round-trip.
- [ ] Define an exact block semantic model between the abstract pipeline and the
  bitstream.
- [ ] Keep the current proved BWT/MTF/RLE core as the mathematical reference.
- [ ] State the refinement target:
  - original proved BWT = reference semantics
  - fast native BWT = executable implementation
  - exact `.bz2` encoder/decoder = wire-format realization of the native layer
- [ ] Add a block-level semantic record for:
  - RLE1-processed data
  - BWT output and `origPtr`
  - used-byte alphabet
  - MTF stream
  - RUNA/RUNB-expanded symbol stream

### 5.2 New correctness lemmas

- [x] Prove initial RLE1 decode(encode xs) = xs.
  - `decodeInitialRLE_encodeInitialRLE` in `Bzip2/Correctness/BZ2/RLE1.lean`,
    via a run-decomposition token model (`runTokens`), a well-formedness
    invariant on chunk streams, and the decoder's inversion of any well-formed
    stream.
- [x] Prove RUNA/RUNB decode(encode xs) = xs.
  - `decodeZeroRun_zeroRunDigits` in `Bzip2/Correctness/BZ2/ZeroRun.lean`
    proves the bijective base-2 RUNA/RUNB digit stream round-trips.
- [x] Prove MTF + RUNA/RUNB payload decode(encode lastColumn) = lastColumn.
  - `decodeMtfBody_encodeMtfRunaRunb` in `Bzip2/Correctness/BZ2/MtfRunaRunb.lean`,
    via a structural model `runaRunbBody` proved equal to the runtime
    index-based `encodeMtfAux`, a pure decoder model mirroring
    `decodeLastColumnLoop`, and reuse of `decodeZeroRun_zeroRunDigits` and
    `mtfDecode_mtfEncode_of_nodup`.
- [ ] Prove used-byte map decode(encode alphabet) = alphabet under validity
  conditions.
- [x] Prove selector MTF decode(encode selectors) = selectors.
  - `decodeSelectors_encodeSelectors` in `Bzip2/Correctness/BZ2/Selectors.lean`:
    a joint move-to-front induction shows the encoder's per-selector indices
    decode back to the selectors, given each is a valid group index. The unary
    bit coding of the indices is closed by `parseSelectors_roundtrip` in
    `Bzip2/Correctness/BZ2/SelectorBits.lean` (full on-the-wire round trip).
- [x] Prove code-length delta-table decode(encode lengths) = lengths.
  - `parseTableCodeLengths_of_prefix` + `writeCodeLengthTable_bits` in
    `Bzip2/Correctness/BZ2/CodeLengths.lean`: the per-symbol unary delta walk
    (`deltaBits`) round-trips at the bit level via `BitsReader`, lifted to the
    full 5-bit-start + per-symbol table. Lengths assumed `≤ 20`.
- [ ] Prove canonical Huffman decode(encode symbols) = symbols.
- [x] Prove bit writer / bit reader roundtrip.
  - Writer side: `Bzip2/Correctness/BZ2/Bits.lean` gives `BitWriter` a
    `List Bool` denotation and proves `writeBit`/`writeBits`/`writeRepeatedBit`
    append exactly the expected bits (with a preserved well-formedness
    invariant).
  - Reader side: `Bzip2/Correctness/BZ2/BitsReader.lean` characterises
    `BitReader` positionally over `bitListOf` (the MSB-first bit list of its
    backing bytes), proving `readBit_eq`, `readBits_eq`, and the headline
    `readBits_of_prefix`: if the cursor bits begin with `natBitsMSB count value`
    (`value < 2^count`), `readBits count` returns `value` and advances past
    exactly those bits. This is the reusable bridge for every metadata parse.
- [ ] Prove block CRC recomputation matches emitted metadata.

### 5.3 Refinement theorems

- [ ] Prove the fast native BWT agrees with the original proved BWT on each
  block.
- [ ] Prove the fast native inverse BWT agrees with the original proved inverse
  BWT on each block.
- [ ] Prove exact block decoder refines abstract block semantics.
- [ ] Prove exact block encoder produces a bitstream representing the same
  abstract block semantics.
- [ ] Prove exact stream decode after exact stream encode returns the original
  bytes.
- [ ] Prove the new decoder agrees with the old proved inverse-BWT core where
  they overlap.

### 5.4 Trust reduction

- [ ] Decide whether Huffman remains a trusted imported component or is proved
  fully inside this project.
- [ ] If trusted temporarily:
  - [ ] isolate it behind a tiny interface
  - [ ] state the exact assumptions
- [ ] If fully internalized:
  - [ ] port/complete codec proofs needed for exact block coding

## Phase 6: Engineering / CLI

- [x] Add command-line entrypoints (`Main.lean` + `Bzip2/CLI.lean`, exe `bzip2`):
  - `compress` (default; in-place `file` → `file.bz2`)
  - `decompress` (`-d`, suffix-based output naming)
  - `test` (`-t`)
  - plus `-k -c -f -q -v -1..-9 -s -L -V --help --`, stdin/stdout filtering,
    clustered short flags, `bunzip2`/`bzcat` argv0 aliasing, and bzip2 exit
    codes (0/1/2/3).
- [x] Add fixture-based integration tests that invoke system `bzip2`.
  - `scripts/run_tests.sh` runs the Lean suites plus a CLI/system-`bzip2`
    smoke matrix; CI now executes it.
- [x] Add benchmarks on representative files (`scripts/bench.sh`: time + ratio
  vs system `bzip2`, cross-decode verified both directions).
- [ ] Add memory/performance notes by block size.
- [x] Add a compatibility matrix in README.

Encoder quality: the block coder now chooses 2–6 Huffman tables with bzip2-style
iterative refinement and per-50-symbol selectors (`planEntropyCoding` in
`Bzip2/Format/BZ2/Encoder.lean`), replacing the earlier degenerate
two-identical-tables path. Output size is at parity with system bzip2 on text
corpora (~99–103%).

## Phase 7: Final Acceptance Checklist

We are done only when all of these are true:

- [x] Our decoder reads `.bz2` produced by Linux `bzip2`.
- [x] Linux `bzip2` / `bunzip2` reads `.bz2` produced by us.
- [x] `bzip2 -t` passes on our output.
- [ ] Small, medium, and large corpus tests pass.
- [ ] Corruption and malformed-input tests pass.
- [ ] Exact stream encode/decode roundtrip theorem is proved.
- [ ] Exact block implementation is connected back to the original BWT-based
  correctness story.

## Immediate Next Task

The industry-standard CLI, multi-table encoder, provability refactors, and the
first correctness proofs (bit-writer denotation, RUNA/RUNB digit round trip)
are landed. The practical inverse-BWT / LF runtime path already exists
(`Bzip2/Format/BZ2/InverseBWT.lean`, O(n) packed T-vector). The remaining work,
in order:

- finish the component round-trip proofs (Phase 5.2): RLE1, MTF/used-byte map,
  selector MTF, canonical Huffman decode, and the reader-side positional bit
  lemmas; these all sit under `Bzip2/Correctness/BZ2/`
- assemble the block- and stream-level headline theorem
  `compress? data = .ok out → decompress? out = .ok data` (Phase 5.2 / 7)
- prove the reference BWT inversion in the origPtr/cyclic formalism (Phase 5.3)
- prove the fast forward BWT refines the reference BWT (Phase 5.3); until then
  it is runtime-validated by the encoder self-check plus the regression corpus
- push the file API toward fully streaming large-file execution (Phase A5:
  `BitWriter` drain, handle-backed `BitSource`, faster canonical decode)
