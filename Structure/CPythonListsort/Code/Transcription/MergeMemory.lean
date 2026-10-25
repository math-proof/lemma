/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean -/

import Def.CPythonListsort.Code.Transcription.TempStorageInvariant
import Def.CPythonListsort.Code.Transcription.MergeMemory.Part2
/-!
# Observable temporary-storage transitions

Allocator failure after a valid request is outside version one. `mergeFreemem`
records the pointer and ownership transition performed by CPython while leaving
the recorded capacity and all unrelated state untouched. `mergeGetmem` retains
the signed capacity-reuse comparison, the unsigned allocation-size guard, and
the fact that the old heap block is freed before that guard is checked.
-/


namespace CPythonListsort

/-- State and return-path information produced by `merge_getmem`. -/
structure MergeGetmemResult (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  outcome : MergeGetmemOutcome

end CPythonListsort
