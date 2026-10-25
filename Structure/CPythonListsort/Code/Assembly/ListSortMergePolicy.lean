/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean -/

import Structure.CPythonListsort.Code.Assembly.ListSortTermination
import Def.CPythonListsort.Code.Assembly.MergePolicyReplay.Part4
import Structure.CPythonListsort.Code.Assembly.ScanPowerForestInvariant.Part2
import Inductive.CPythonListsort.Code.Assembly.ListSortScanReached
import Def.CPythonListsort.Code.Assembly.ListSortMergePolicy
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

/-! ## Whole-scan split at the real final-collapse boundary -/

/-- A successful scan trace is split at the exact call boundary where
`list_sort_impl` enters `merge_force_collapse`.  `scanEvents` includes every
actual `found_new_run` merge and every rich formed-run observation; the
`collapseEvents` suffix is literally the traced final-collapse call. -/
structure ListSortScanPolicyReplayWitness
    (input : RunSpan) (initialForest : List SpannedMergeTree)
    (execution : TraceResult (ListSortImplResult κ ν))
    (openState : MergeState κ ν)
    (openForest closedForest : List SpannedMergeTree)
    (scanEvents collapseEvents : List PolicyEvent)
    (collapsed : MergeForceCollapseResult κ ν) : Prop where
  traceSplit :
    execution.trace.policyEvents = scanEvents ++ collapseEvents
  scanReplay :
    replayPolicyEventsFrom? input initialForest scanEvents = some openForest
  openMatch : PolicyForestMatches openForest openState
  openLayout : PendingLayout openState input.len
  openPowered : PoweredPrefix openState
  collapseSafety :
    MergeForceCollapseSafetyPost openState input.len collapsed
  collapseEvents_eq :
    collapseEvents =
      (mergeForceCollapseTraced? openState).trace.policyEvents
  collapseReplay :
    replayPolicyEventsFrom? input openForest collapseEvents =
      some closedForest
  closedMatch : PolicyForestMatches closedForest collapsed.state

end CPythonListsort
