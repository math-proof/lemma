/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean -/

import Inductive.CPythonListsort.Code.Assembly.MergeTreeCost
import Def.CPythonListsort.Code.Transcription.Powerloop
import Mathlib.Tactic
import Def.CPythonListsort.Code.Assembly.MergePolicyReplay
/-!
# Checked replay of the interleaved PowerSort policy trace

The access trace records formed-run pushes and logical, pre-trimming merges in
one chronological channel.  This module gives that raw channel a deliberately
strict, pure semantics.  A formed-run observation is accepted only when its
post-push depth, source interval, adaptive-minrun branch, and remaining-input
metadata agree.  A merge is accepted only when its index and full source
spans identify an adjacent pair in the current forest.

Every replayed internal node is labelled by the transcribed `powerloop`
applied to the aggregate spans being merged.  No label supplied by the trace
is trusted, and physical trimming does not alter the logical merge cost.
-/

/-! ## Raw event projections -/


namespace CPythonListsort

namespace PolicyEvent

instance (push : PendingPushEvent) : Decidable (FormedLengthRelation push) :=
  inferInstanceAs (Decidable
    (0 < push.naturalLength ∧ push.naturalLength ≤ push.remainingBefore ∧
      0 < push.target ∧
      ((push.naturalLength < push.target ∧
          push.run.len = min push.remainingBefore push.target) ∨
        (push.target ≤ push.naturalLength ∧
          push.run.len = push.naturalLength))))

end PolicyEvent
end CPythonListsort
