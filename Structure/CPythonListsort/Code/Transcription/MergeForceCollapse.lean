/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeForceCollapse.lean -/

import Theorem.CPythonListsort.Code.Transcription.MergeAt
/-!
# Final pending-stack collapse

This module transcribes `merge_force_collapse`: until one pending run remains,
choose one of the top two adjacent merge positions using the neighboring run
lengths and call `merge_at`.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Observable result of `merge_force_collapse`. -/
structure MergeForceCollapseResult (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  returnCode : Int
  fuelExhausted : Bool

end CPythonListsort
