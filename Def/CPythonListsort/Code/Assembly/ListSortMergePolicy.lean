/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean -/

import Structure.CPythonListsort.Code.Assembly.ListSortTermination
import Def.CPythonListsort.Code.Assembly.MergePolicyReplay.Part4
import Structure.CPythonListsort.Code.Assembly.ScanPowerForestInvariant.Part2
import Inductive.CPythonListsort.Code.Assembly.ListSortScanReached
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

/-! ## Top-level empty/singleton normalization -/

/-- Paper-facing formed-run lengths for a real top-level execution.

Inputs of length zero and one bypass the scan, so their genuine policy-event
stream is empty.  The singleton leaf is introduced only at this semantic
normalization boundary; no synthetic `.formed` observation is added to the
machine trace. -/
def topLevelFormedLengths (input : RunSpan)
    (events : List PolicyEvent) : List Nat :=
  if input.len = 0 then []
  else if input.len = 1 then [1]
  else PolicyEvent.formedLengths events

/-- Normalize the real top-level policy stream to an empty-or-tree merge plan.

For the two scan-bypass cases the empty event stream means `.empty` at length
zero and one literal leaf at length one.  Larger inputs use the checked replay
without alteration. -/
def replayTopLevelMergePlan? (input : RunSpan)
    (events : List PolicyEvent) : Option MergePlan :=
  if input.len = 0 then
    if events = [] then some .empty else none
  else if input.len = 1 then
    if events = [] then some (.tree (.leaf 1)) else none
  else
    replayMergePlan? input events

/-- A replay forest represents exactly the pending stack of a machine state,
after forgetting the pending runs' stored boundary powers. -/
def PolicyForestMatches (forest : List SpannedMergeTree)
    (state : MergeState κ ν) : Prop :=
  forest.map SpannedMergeTree.span =
    state.pending.toList.map RunSpan.ofPendingRun

/-! ## `found_new_run` merge segment -/

/- The actual stack between two iterations of `found_new_run` is not yet a
steady open PowerSort forest: its newest root may be an internal tree, and
the stored power on that run is stale until the terminal write.  This private
ghost keeps exactly the extra historical facts needed to justify the next
top merge. -/
def FoundPowerForestInv (input : RunSpan) (prospectivePower : Nat)
    (newRun : PendingRun) (forest : List SpannedMergeTree)
    (state : MergeState κ ν) : Prop :=
  input.len ≤ PY_LIST_MAX ∧
    state.basekeys = input.base ∧
    state.listlen = BitVec.ofNat 64 input.len ∧
    ∃ beforeForest topTree beforeRuns topRun,
      forest = beforeForest ++ [topTree] ∧
      state.pending.toList = beforeRuns ++ [topRun] ∧
      prospectivePower = pendingBoundaryPower state.basekeys state.listlen
        topRun newRun ∧
      List.Forall₂ (RunTreeAligned input) beforeForest beforeRuns ∧
      topTree.span = RunSpan.ofPendingRun topRun ∧
      topTree.Valid ∧
      topTree.tree.PowerValid input.base (BitVec.ofNat 64 input.len)
        topTree.span.base ∧
      (∀ rootPower, topTree.tree.rootPower = some rootPower →
        prospectivePower < rootPower) ∧
      (∀ run ∈ beforeRuns, ∀ storedPower rootPower,
        run.power = some storedPower →
          topTree.tree.rootPower = some rootPower → storedPower < rootPower)

end CPythonListsort
