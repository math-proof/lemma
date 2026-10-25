/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean -/

import Def.CPythonListsort.Code.Transcription.TempStorageInvariant
import Def.CPythonListsort.Code.Transcription.MergeMemory
/-!
# Observable temporary-storage transitions

Allocator failure after a valid request is outside version one. `mergeFreemem`
records the pointer and ownership transition performed by CPython while leaving
the recorded capacity and all unrelated state untouched. `mergeGetmem` retains
the signed capacity-reuse comparison, the unsigned allocation-size guard, and
the fact that the old heap block is freed before that guard is checked.
-/


namespace CPythonListsort

/-! ## `merge_getmem` -/

/-- Observable control-flow outcome of `merge_getmem`. The `.grown` case is the
version-one successful-allocation abstraction. `.guardRejected` is not an
allocator failure: it is the deterministic `size_t` overflow guard from the C
source, which runs after `merge_freemem`. -/
inductive MergeGetmemOutcome where
  | reused
  | grown
  | guardRejected
  deriving DecidableEq, Repr

end CPythonListsort
