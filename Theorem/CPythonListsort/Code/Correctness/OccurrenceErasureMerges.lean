/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean -/

import Def.CPythonListsort.Code.Correctness.OccurrenceErasure
import Def.CPythonListsort.Code.Correctness.OccurrenceErasureMerges
/-!
# Occurrence-tag erasure for merge evaluators

The functional-correctness development carries ghost origins in its keys.
This module proves that temporary-storage allocation, galloping, and both
concrete merge engines commute with erasing those origins.
These are evaluator equations only: no ordering or stability law is assumed.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

@[simp] theorem eraseOccurrenceMergeLoResult_state (result : MergeLoResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeLoResult result).state =
      eraseOccurrenceMergeState result.state := rfl

end CPythonListsort
