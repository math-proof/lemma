/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean -/

import Def.CPythonListsort.Code.Transcription.TempStorageInvariant
import Inductive.CPythonListsort.Code.Transcription.MergeMemory
/-!
# Observable temporary-storage transitions

Allocator failure after a valid request is outside version one. `mergeFreemem`
records the pointer and ownership transition performed by CPython while leaving
the recorded capacity and all unrelated state untouched. `mergeGetmem` retains
the signed capacity-reuse comparison, the unsigned allocation-size guard, and
the fact that the old heap block is freed before that guard is checked.
-/


namespace CPythonListsort

/-- Site-tagged same-store movement.  The tag carries review provenance only;
the evaluator is definitionally the existing overlap-safe primitive. -/
def mergeDataMemmove? (_site : MergeMemmoveCallsite)
    (data : SortSlice κ ν) (dst src : Int) (count : Nat) :
    Option (SortSlice κ ν) :=
  data.memmove? dst src count

/-- Transcription of `merge_freemem`. Inline storage is retained. Any
non-inline key storage is released and its allocated cells cease to be
accessible; `alloced` and `hasValues` are intentionally unchanged. -/
def mergeFreemem (state : MergeState κ ν) : MergeState κ ν :=
  if state.a.backing = .inline then
    state
  else
    { state with
      a := { state.a with cells := #[], backing := .released } }

end CPythonListsort
