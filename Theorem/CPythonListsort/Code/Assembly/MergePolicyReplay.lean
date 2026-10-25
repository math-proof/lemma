/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean -/

import Inductive.CPythonListsort.Code.Assembly.MergeTreeCost
import Def.CPythonListsort.Code.Transcription.Powerloop
import Mathlib.Tactic
import Def.CPythonListsort.Code.Assembly.MergePolicyReplay.Part3
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

/-- Exact success characterization for one formed-run event. -/
theorem applyPolicyEvent_formed_eq_some_iff
    (input : RunSpan) (forest result : List SpannedMergeTree)
    (push : PendingPushEvent) :
    applyPolicyEvent? input forest (.formed push) = some result ↔
      ValidFormedEvent input forest push ∧
        result = forest ++ [SpannedMergeTree.leaf push.run] := by
  simp [applyPolicyEvent?, eq_comm]

/-- Replaying concatenated event segments is exactly sequential replay. -/
theorem replayPolicyEventsFrom_append (input : RunSpan)
    (forest : List SpannedMergeTree) (first second : List PolicyEvent) :
    replayPolicyEventsFrom? input forest (first ++ second) =
      (replayPolicyEventsFrom? input forest first).bind fun middle =>
        replayPolicyEventsFrom? input middle second := by
  induction first generalizing forest with
  | nil => rfl
  | cons event events ih =>
      simp only [List.cons_append, replayPolicyEventsFrom?]
      cases hstep : applyPolicyEvent? input forest event with
      | none => simp
      | some middle => simpa using ih middle

/-- Every formed-run observation accepted by a successful replay satisfies
the exact adaptive-minrun branch equation recorded in that observation.  This
exports the arithmetic check performed by `applyPolicyEvent?`; downstream
cost theorems therefore need not treat the trace metadata as trusted prose. -/
theorem replayPolicyEventsFrom_formedLengthRelation
    {input : RunSpan} {initial result : List SpannedMergeTree}
    {events : List PolicyEvent}
    (hreplay : replayPolicyEventsFrom? input initial events = some result) :
    ∀ push, .formed push ∈ events → FormedLengthRelation push := by
  induction events generalizing initial with
  | nil => simp
  | cons event events ih =>
      simp only [replayPolicyEventsFrom?] at hreplay
      cases hstep : applyPolicyEvent? input initial event with
      | none => simp [hstep] at hreplay
      | some middle =>
          rw [hstep] at hreplay
          intro push hpush
          simp only [List.mem_cons] at hpush
          rcases hpush with hhead | htail
          · cases event with
            | formed observed =>
                cases hhead
                exact
                  ((applyPolicyEvent_formed_eq_some_iff input initial middle
                    push).mp hstep).1.2.2.2.2.2
            | merge observed => contradiction
          · exact ih hreplay push htail

end PolicyEvent
end CPythonListsort
