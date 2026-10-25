/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean -/

import Def.CPythonListsort.Code.Transcription.TempStorageInvariant
/-!
# Observable temporary-storage transitions

Allocator failure after a valid request is outside version one. `mergeFreemem`
records the pointer and ownership transition performed by CPython while leaving
the recorded capacity and all unrelated state untouched. `mergeGetmem` retains
the signed capacity-reuse comparison, the unsigned allocation-size guard, and
the fact that the old heap block is freed before that guard is checked.
-/


namespace CPythonListsort

/-! ## Same-store merge movement provenance -/

/-- The four block-movement sites whose source and destination are both in
`MergeState.data`.  They are deliberately separate from the six tagged
temp/main `memcpy` sites: these calls require overlap-safe `memmove` semantics. -/
inductive MergeMemmoveCallsite where
  | loGallopB
  | loCopyBTail
  | hiGallopA
  | hiCopyATail
  deriving DecidableEq, Repr

end CPythonListsort
