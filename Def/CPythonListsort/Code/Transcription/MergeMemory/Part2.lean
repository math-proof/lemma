/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean -/

import Def.CPythonListsort.Code.Transcription.TempStorageInvariant
import Inductive.CPythonListsort.Code.Transcription.MergeMemory.Part2
/-!
# Observable temporary-storage transitions

Allocator failure after a valid request is outside version one. `mergeFreemem`
records the pointer and ownership transition performed by CPython while leaving
the recorded capacity and all unrelated state untouched. `mergeGetmem` retains
the signed capacity-reuse comparison, the unsigned allocation-size guard, and
the fact that the old heap block is freed before that guard is checked.
-/


namespace CPythonListsort

/-- C integer returned on each modeled path. Both successful paths return zero;
the deterministic allocation-size rejection returns minus one. -/
def MergeGetmemOutcome.returnCode : MergeGetmemOutcome → Int
  | .reused | .grown => 0
  | .guardRejected => -1

end CPythonListsort
