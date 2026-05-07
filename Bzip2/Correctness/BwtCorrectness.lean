import Bzip2.Correctness.RLE
import Bzip2.Correctness.MTF
import Bzip2.Correctness.Inverse

/-!
This file assembles the correctness results for the individual compression
stages into the final end-to-end theorem
`decompress (compress xs) = xs`.
-/

namespace Bzip2

set_option autoImplicit false

variable {α : Type} [LinearOrder α] [DecidableEq α]

/-- End-to-end compression/decompression round-trip theorem. -/
theorem decompress_compress_eq (xs : List α) :
    decompress (compress xs) = xs := by
  let alphabet : List (Symbol α) := (withSentinel xs).eraseDups.mergeSort (· ≤ ·)
  have halphaNodup : alphabet.Nodup := by
    simp_all only [List.nodup_mergeSort, alphabet]
    exact nodup_eraseDups (withSentinel xs)
  have hlastMem : ∀ c ∈ (transform xs).last, c ∈ alphabet := by
    grind only [!transform_last_perm_withSentinel, List.mem_mergeSort, mem_eraseDups, usr List.Perm.mem_iff]
  have hmtf :
      mtfDecode alphabet (mtfEncode alphabet (transform xs).last) = (transform xs).last := by
    exact mtfDecode_mtfEncode_of_nodup alphabet (transform xs).last halphaNodup hlastMem
  grind only [compress, decompress, !inverse_transform_from_LF, !rleDecode_rleEncode, inverse,
    inverseAlgorithmic]

end Bzip2
