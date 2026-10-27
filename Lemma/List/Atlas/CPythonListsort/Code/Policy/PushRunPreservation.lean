import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.CPythonListsort.Code.Policy.PushRunPreservation
open CPythonListsort


namespace CPythonListsort

/--
[PendingRunsCover.appendSingleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/PushRunPreservation.lean)
-/
@[path]
lemma PendingRunsCover.appendSingleton
  {cursor limit : Nat}
  {runs : List PendingRun}
  {newRun : PendingRun}
-- given
  (hcover : PendingRunsCover cursor limit runs)
  (hbase : newRun.base = limit)
  (hnonnegative : newRun.len.Nonnegative)
  (hpositive : 0 < newRun.len.toNat) :
-- imply
  PendingRunsCover cursor (limit + newRun.len.toNat) (runs ++ [newRun]) := by
-- proof
  induction runs generalizing cursor with
  | nil =>
    simp only [PendingRunsCover] at hcover
    subst cursor
    simp [PendingRunsCover, PendingRun.endIndex, hbase, hnonnegative,
      hpositive]
  | cons run runs ih =>
    simp only [List.cons_append, PendingRunsCover] at hcover ⊢
    rcases hcover with
      ⟨hrunBase, hrunNonnegative, hrunPositive, hrunEnd, hrest⟩
    refine
      ⟨hrunBase, hrunNonnegative, hrunPositive, ?_,
        ih hrest⟩
    omega

end CPythonListsort

namespace CPythonListsort

/--
[pushPendingRun_restores_poweredPrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/PushRunPreservation.lean)
-/
@[path]
lemma pushPendingRun_restores_poweredPrefix
  {state : MergeState κ ν}
  {scanned : Nat}
  {newRun : PendingRun}
-- given
  (hready : ReadyToPush state scanned newRun) :
-- imply
  PoweredPrefix (pushPendingRun state newRun) := by
-- proof
  right
  refine
    ⟨state.pending.toList, newRun, ?_, hready.current_powers, ?_⟩
  · simp [pushPendingRun]
  · simpa [pushPendingRun] using hready.virtual_boundary_powers

end CPythonListsort

namespace CPythonListsort

/--
[pushPendingRun_preserves_policy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/PushRunPreservation.lean)
-/
@[path]
lemma pushPendingRun_preserves_policy
  {state : MergeState κ ν}
  {scanned : Nat}
  {newRun : PendingRun}
-- given
  (hready : ReadyToPush state scanned newRun) :
-- imply
  let pushed := pushPendingRun state newRun pushed.pending.toList = state.pending.toList ++ [newRun] ∧ PendingLayout pushed (scanned + newRun.len.toNat) ∧ PoweredPrefix pushed ∧ pushed.pending.size = state.pending.size + 1 ∧ pushed.pending.size ≤ 61 ∧ pushed.pending.size < MAX_MERGE_PENDING := by
-- proof
  dsimp only
  have hdepth := readyToPush_stack_depth_bound state scanned newRun hready
  exact
    ⟨by simp [pushPendingRun],
      pushPendingRun_preserves_pendingLayout state scanned newRun hready,
      pushPendingRun_restores_poweredPrefix state scanned newRun hready,
      hdepth.2.1, hdepth.2.2.1, hdepth.2.2.2⟩

end CPythonListsort

namespace CPythonListsort

/--
[pushPendingRunTraced_is_total](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/PushRunPreservation.lean)
-/
@[path]
lemma pushPendingRunTraced_is_total
  {state : MergeState κ ν}
  {newRun : PendingRun} :
-- imply
  (pushPendingRunTraced state newRun).result = some (pushPendingRun state newRun) ∧ (pushPendingRunTraced state newRun).trace.pushDepths = [state.pending.size + 1] ∧ (pushPendingRunTraced state newRun).trace.stackDepthMax = state.pending.size + 1 := by
-- proof
  simp [pushPendingRunTraced, pushPendingRun, AccessTrace.singletonPushDepth,
    AccessTrace.stackDepthMax]

end CPythonListsort

namespace CPythonListsort

/--
[pushPendingRunTraced_preserves_policy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/PushRunPreservation.lean)
-/
@[path]
lemma pushPendingRunTraced_preserves_policy
  {state : MergeState κ ν}
  {scanned : Nat}
  {newRun : PendingRun}
-- given
  (hready : ReadyToPush state scanned newRun) :
-- imply
  let traced := pushPendingRunTraced state newRun traced.result = some (pushPendingRun state newRun) ∧ traced.trace.pushDepths = [state.pending.size + 1] ∧ traced.trace.stackDepthMax = state.pending.size + 1 ∧ traced.trace.stackDepthMax ≤ 61 ∧ traced.trace.stackDepthMax < MAX_MERGE_PENDING ∧ PendingLayout (pushPendingRun state newRun) (scanned + newRun.len.toNat) ∧ PoweredPrefix (pushPendingRun state newRun) := by
-- proof
  dsimp only
  have htotal := pushPendingRunTraced_is_total state newRun
  have hpolicy := pushPendingRun_preserves_policy state scanned newRun hready
  have hdepth := readyToPush_stack_depth_bound state scanned newRun hready
  refine
    ⟨htotal.1, htotal.2.1, htotal.2.2, ?_, ?_, hpolicy.2.1,
      hpolicy.2.2.1⟩
  · rw [htotal.2.2]
    rwa [← hdepth.2.1]
  · rw [htotal.2.2]
    rwa [← hdepth.2.1]

end CPythonListsort

/--
[pushPendingRun_preserves_pendingLayout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/PushRunPreservation.lean)
-/
@[path]
private lemma pushPendingRun_preserves_pendingLayout_eq
  {state : MergeState κ ν}
  {scanned : Nat}
  {newRun : PendingRun}
-- given
  (hready : ReadyToPush state scanned newRun) :
-- imply
  PendingLayout (pushPendingRun state newRun) (scanned + newRun.len.toNat) := by
-- proof
  apply CPythonListsort.pushPendingRun_preserves_pendingLayout state scanned newRun hready


-- created on 2026-10-23
