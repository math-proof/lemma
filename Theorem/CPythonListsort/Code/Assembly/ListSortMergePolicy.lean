/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean -/

import Structure.CPythonListsort.Code.Assembly.ListSortTermination
import Def.CPythonListsort.Code.Assembly.MergePolicyReplay.Part4
import Structure.CPythonListsort.Code.Assembly.ScanPowerForestInvariant.Part2
import Inductive.CPythonListsort.Code.Assembly.ListSortScanReached
import Def.CPythonListsort.Code.Assembly.ListSortMergePolicy.Part3
/-!
# The real `list_sort_impl` policy trace replays

This module connects the chronological `.formed`/`.merge` observations made
by the genuine traced evaluator to the pure checked replay in
`MergePolicyReplay`.  The bridge is deliberately comparator-agnostic: it uses
the pending-layout and storage hypotheses already discharged by the public
safety theorem, but assumes no order law.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- The historical scan certificate exposes the complete valid PowerSort
open forest at the exact reached final-collapse boundary. -/
theorem ListSortScanStrongWitness.openPowerValid
    {input : RunSpan} {initialForest : List SpannedMergeTree}
    {reverse : Bool} {inputSize : Nat}
    {execution : TraceResult (ListSortImplResult κ ν)}
    {openState : MergeState κ ν}
    {openForest closedForest : List SpannedMergeTree}
    {scanEvents collapseEvents : List PolicyEvent}
    {collapsed : MergeForceCollapseResult κ ν}
    (witness : ListSortScanStrongWitness input initialForest reverse inputSize
      execution openState openForest closedForest scanEvents collapseEvents
      collapsed) :
    PowerOpenForestValid input openForest := by
  exact witness.openPowerInv.toPowerOpenForestValid
    witness.replay.openLayout witness.replay.openPowered

/-- The split certificate exposes, without another evaluator inspection, the
exact adaptive-minrun equation for every formed event in the scan prefix. -/
theorem ListSortScanPolicyReplayPost.formedLengthRelation
    {input : RunSpan} {initialForest : List SpannedMergeTree}
    {fuel : Nat} {state : MergeState κ ν} {lo remaining : Nat}
    {reverse : Bool} {inputSize : Nat}
    (post : ListSortScanPolicyReplayPost input initialForest fuel state lo
      remaining reverse inputSize) :
    ∀ push,
      PolicyEvent.formed push ∈
          (listSortScanTraced? fuel state lo remaining reverse
            inputSize).trace.policyEvents →
        FormedLengthRelation push := by
  rcases post with
    ⟨openState, openForest, closedForest, scanEvents, collapseEvents,
      collapsed, witness⟩
  have hreplay : replayPolicyEventsFrom? input initialForest
      ((listSortScanTraced? fuel state lo remaining reverse
        inputSize).trace.policyEvents) = some closedForest := by
    rw [witness.traceSplit, replayPolicyEventsFrom_append,
      witness.scanReplay]
    exact witness.collapseReplay
  exact replayPolicyEventsFrom_formedLengthRelation hreplay

end CPythonListsort
