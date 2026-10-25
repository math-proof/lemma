/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelMerges.lean -/

import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part6
import Def.CPythonListsort.Code.Correctness.OriginRelabelMerges
/-!
# Origin-relabel equivariance for merge evaluators

The reverse-mode transport changes only the recorded origins carried by
occurrence keys.  This module proves that temporary-storage allocation,
galloping, and both concrete merge engines commute with that relabeling.
These are evaluator equations only: no ordering or stability law is assumed.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

@[simp] theorem mirrorMergeGetmemResult_state (size : Nat)
    (result : MergeGetmemResult (Occurrence alpha) nu) :
    (mirrorMergeGetmemResult size result).state =
      mirrorMergeState size result.state := rfl

@[simp] theorem mirrorMergeGetmemResult_outcome (size : Nat)
    (result : MergeGetmemResult (Occurrence alpha) nu) :
    (mirrorMergeGetmemResult size result).outcome = result.outcome := rfl

end CPythonListsort
