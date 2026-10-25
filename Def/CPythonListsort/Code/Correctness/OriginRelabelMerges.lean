/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelMerges.lean -/

import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part6
import Theorem.CPythonListsort.Code.Correctness.OriginRelabelMerges
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

/-! ## Temporary storage and allocation -/

/-- Relabel the state component returned by `mergeGetmem`. -/
def mirrorMergeGetmemResult (size : Nat)
    (result : MergeGetmemResult (Occurrence alpha) nu) :
    MergeGetmemResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

end CPythonListsort
