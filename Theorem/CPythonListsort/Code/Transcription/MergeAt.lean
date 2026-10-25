/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean -/

import Def.CPythonListsort.Code.Transcription.MergeHi.Part6
import Def.CPythonListsort.Code.Transcription.MergeLo.Part6
import Def.CPythonListsort.Code.Transcription.MergeAt.Part4
/-!
# Pending-stack merge dispatch

This module transcribes CPython's `merge_at`.  The pending-stack replacement
happens before either galloping search, exactly as it does in C, so a later
modeled failure retains that mutation.  The two searches trim entries already
in their final positions and the shorter remaining run selects `merge_lo` or
`merge_hi`.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

set_option linter.style.nativeDecide false in
/-- Concrete regression: the exposed preparation path can reach the
`merge_lo` call site with nonempty post-trim runs. -/
example :
    (prepareMergeAt? mergeAtLoPreparationExampleState 0).bind
      mergeAtPreparationShape = some (true, 2, 2) := by
  decide

set_option linter.style.nativeDecide false in
/-- Concrete regression: the exposed preparation path can also reach the
strict complementary `merge_hi` call site. -/
example :
    (prepareMergeAt? mergeAtHiPreparationExampleState 0).bind
      mergeAtPreparationShape = some (false, 3, 2) := by
  decide

end CPythonListsort
