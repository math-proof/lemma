/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean -/

import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Mathlib
import Structure.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
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

namespace MergeGetmemStoragePost

variable {before : MergeState κ ν} {need : PySSize}
  {result : MergeGetmemResult κ ν}

/-! ## Regression: why live input is essential -/

/-- A concrete impossible-at-a-merge-boundary state: `alloced` remains eight,
as it can after `merge_freemem`, while the payload is empty and released. -/
def fabricatedStaleReleasedMergeState : MergeState Unit Unit :=
  { min_gallop := MIN_GALLOP
    listlen := 0
    basekeys := 0
    data := { entries := #[] }
    a :=
      { cells := #[]
        backing := .released
        hasValues := false }
    alloced := 8
    pending := #[]
    key_compare := fun _ _ => false
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

end MergeGetmemStoragePost
end CPythonListsort
