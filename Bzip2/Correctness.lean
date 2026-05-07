import Bzip2.Correctness.RLE
import Bzip2.Correctness.MTF
import Bzip2.Correctness.Matrix
import Bzip2.Correctness.LF
import Bzip2.Correctness.Inverse
import Bzip2.Correctness.BwtCorrectness

/-!
# Bzip2.Correctness

Proof layer for the abstract compression pipeline.

This module assembles the stage-wise correctness developments and the final
end-to-end theorem `decompress_compress_eq`.
-/
