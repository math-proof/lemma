/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean -/

import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Mathlib
import Structure.CPythonListsort.Code.Assembly.MergeGetmemStorageValid
/-!
# `merge_getmem` storage validity

This module assembles the representation and liveness facts for the two
successful `merge_getmem` paths.  Reuse is safe only from live input storage:
the raw transcription intentionally admits a fabricated released state with a
stale `alloced`, but none of the theorems here do.  Growth uses the exact
allocation-limit premise supplied by the call-site request-bound theorem.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Project the non-storage frame preserved by `merge_getmem`. -/
def MergeState.mergeGetmemNonStorageFrame (state : MergeState κ ν) :
    MergeGetmemNonStorageFrame κ ν :=
  { min_gallop := state.min_gallop
    listlen := state.listlen
    basekeys := state.basekeys
    data := state.data
    pending := state.pending
    key_compare := state.key_compare
    mr_current := state.mr_current
    mr_e := state.mr_e
    mr_mask := state.mr_mask }

end CPythonListsort
