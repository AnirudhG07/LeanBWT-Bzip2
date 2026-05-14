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

The outer stream is now `.bz2`-like, but the inside of each block is still not
real bzip2. The remaining work is to replace the current custom block body with
the actual bzip2 block coding:

- initial RLE1 before BWT
- post-MTF RUNA/RUNB encoding
- end-of-block symbol
- 2 to 6 Huffman tables
- selector list for groups of 50 symbols
- canonical Huffman code-length encoding
- exact bit-level packing

## Recommended Order

Do this in order:

1. Exact decoder for real `.bz2` blocks.
2. Exact encoder for real `.bz2` blocks.
3. Fast native BWT / inverse-BWT implementation for practical execution.
4. Refinement proofs from abstract pipeline to real implementation.
5. Large interoperability and regression test suite.

Decoder-first is the right order because it gives us the exact wire-format model
and lets us validate against system-produced `.bz2` files before we try to emit
them.

Now that exact `.bz2` interoperability is in place for practical small/medium
inputs, the next scaling step is the fast native BWT layer.

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

- [ ] multi-megabyte text
- [ ] multi-megabyte binary
- [ ] highly repetitive large file
- [ ] incompressible large file
- [ ] files spanning many blocks

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

- [ ] Prove initial RLE1 decode(encode xs) = xs.
- [ ] Prove RUNA/RUNB decode(encode xs) = xs.
- [ ] Prove used-byte map decode(encode alphabet) = alphabet under validity
  conditions.
- [ ] Prove selector MTF decode(encode selectors) = selectors.
- [ ] Prove canonical Huffman decode(encode symbols) = symbols.
- [ ] Prove bit writer / bit reader roundtrip.
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

- [ ] Add command-line entrypoints:
  - `compress`
  - `decompress`
  - `test`
- [ ] Add fixture-based integration tests that invoke system `bzip2`.
- [ ] Add benchmarks on representative files.
- [ ] Add memory/performance notes by block size.
- [ ] Add a compatibility matrix in README.

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

Start the fast native BWT split and the proof bridge:

- add a new practical BWT / inverse-BWT implementation for execution without deleting the current proved construction
- keep the original BWT development as the reference semantics for proofs
- switch the executable exact encoder/decoder to the fast block-sorting BWT once it exists
- then connect the fast BWT back to the reference BWT by refinement theorems
- enable the currently guarded large-file exact interoperability tests after that native path lands
