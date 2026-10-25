/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeForceCollapse.lean -/

import Theorem.CPythonListsort.Code.Transcription.MergeAt
import Def.CPythonListsort.Code.Transcription.MergeForceCollapse
/-!
# Final pending-stack collapse

This module transcribes `merge_force_collapse`: until one pending run remains,
choose one of the top two adjacent merge positions using the neighboring run
lengths and call `merge_at`.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

set_option linter.style.nativeDecide false in
/-- The neighboring-length test is strict: a tie keeps `n = size - 2` and
therefore chooses the top pair rather than the lower pair. -/
example : forceCollapseIndex? forceCollapseTieExampleState = some 1 := by
  decide

end CPythonListsort
