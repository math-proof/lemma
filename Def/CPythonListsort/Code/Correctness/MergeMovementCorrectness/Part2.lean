/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean -/

import Def.CPythonListsort.Code.Transcription.MergeLo.Part6
import Def.CPythonListsort.Code.Transcription.MergeHi.Part6
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Structure.CPythonListsort.Code.Correctness.MergeMovementCorrectness
/-!
# Exact semantics of merge movement primitives

The safety layer proves that merge reads and writes stay within their allocated
backings.  Functional merge proofs additionally need the exact whole-entry
effect of those movements.  This module records that effect against the input
snapshot: a successful movement copies each key/payload pair from its original
source position and changes no position outside its destination range.

The signed, pointwise predicates below match the pointer-shaped transcription.
Natural-indexed `SortSlice.EqualOutsideRange` consequences are supplied for
the range-facing correctness layer.
-/


namespace CPythonListsort

universe u v

variable {kappa : Type u} {nu : Type v}

/-! ## Executable overlap regression -/

def mergeMovementOverlapInput : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := some 10 },
        { key := 2, value := some 20 },
        { key := 3, value := some 30 },
        { key := 4, value := some 40 },
        { key := 5, value := some 50 }] }

end CPythonListsort
