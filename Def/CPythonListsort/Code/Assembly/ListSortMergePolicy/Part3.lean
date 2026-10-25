/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean -/

import Structure.CPythonListsort.Code.Assembly.ListSortTermination
import Def.CPythonListsort.Code.Assembly.MergePolicyReplay.Part4
import Structure.CPythonListsort.Code.Assembly.ScanPowerForestInvariant.Part2
import Inductive.CPythonListsort.Code.Assembly.ListSortScanReached
import Structure.CPythonListsort.Code.Assembly.ListSortMergePolicy.Part2
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

def StrongPolicyTraceReplaySplit
    (input : RunSpan) (initialForest : List SpannedMergeTree)
    (reverse : Bool) (inputSize : Nat)
    (execution : TraceResult (ListSortImplResult κ ν)) : Prop :=
  ∃ (openState : MergeState κ ν)
    (openForest closedForest : List SpannedMergeTree)
    (scanEvents collapseEvents : List PolicyEvent)
    (collapsed : MergeForceCollapseResult κ ν),
    ListSortScanStrongWitness input initialForest reverse inputSize execution
      openState openForest closedForest scanEvents collapseEvents collapsed

def ListSortScanStrongPost
    (input : RunSpan) (initialForest : List SpannedMergeTree)
    (fuel : Nat) (state : MergeState κ ν) (lo remaining : Nat)
    (reverse : Bool) (inputSize : Nat) : Prop :=
  StrongPolicyTraceReplaySplit input initialForest reverse inputSize
    (listSortScanTraced? fuel state lo remaining reverse inputSize)

end CPythonListsort
