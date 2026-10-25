/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean -/

import Structure.CPythonListsort.Code.Assembly.ListSortTermination
import Def.CPythonListsort.Code.Assembly.MergePolicyReplay.Part4
import Structure.CPythonListsort.Code.Assembly.ScanPowerForestInvariant.Part2
import Inductive.CPythonListsort.Code.Assembly.ListSortScanReached
import Def.CPythonListsort.Code.Assembly.ListSortMergePolicy.Part2
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

/-- Strong scan witness: the replay split is supplemented by the historical
PowerSort forest carried by the real scan and an execution-indexed proof that
the displayed open state is the state actually passed to final collapse.

Unlike `PolicyTraceReplaySplit`, this structure has no transport theorem from
policy-event equality alone. -/
structure ListSortScanStrongWitness
    (input : RunSpan) (initialForest : List SpannedMergeTree)
    (reverse : Bool) (inputSize : Nat)
    (execution : TraceResult (ListSortImplResult κ ν))
    (openState : MergeState κ ν)
    (openForest closedForest : List SpannedMergeTree)
    (scanEvents collapseEvents : List PolicyEvent)
    (collapsed : MergeForceCollapseResult κ ν) : Prop where
  replay : ListSortScanPolicyReplayWitness input initialForest execution
    openState openForest closedForest scanEvents collapseEvents collapsed
  openPowerInv : ScanPowerForestInv input openForest openState
  openTempInvariant : TempStorageInv openState.a openState.alloced
  openTempLive : openState.a.Live
  openValuesMode :
    SortSlice.ValuesModeInvariant openState.a.hasValues openState.data
  collapseFormedLengths : PolicyEvent.formedLengths collapseEvents = []
  reachedCollapse : ListSortScanReachedCollapse reverse inputSize openState
    collapsed execution

end CPythonListsort
