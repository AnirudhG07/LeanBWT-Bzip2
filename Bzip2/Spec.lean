import Bzip2.BWT

/-!
# Bzip2.Spec

Frozen semantic specification layer for this project.

This module exposes the abstract list-based Burrows-Wheeler / MTF / RLE model
implemented in `Bzip2.BWT`. It is the mathematical reference that the native
byte-level and future exact `.bz2` implementations are expected to refine.
-/
