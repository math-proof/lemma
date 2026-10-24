/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.ListSortTermination
import sympy.atlas.CPythonListsort.Code.Assembly.MergePolicyReplay
import sympy.atlas.CPythonListsort.Code.Assembly.ScanPowerForestInvariant
import sympy.atlas.CPythonListsort.Code.Assembly.ListSortScanReached

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
private def FoundPowerForestInv (input : RunSpan) (prospectivePower : Nat)
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

/-- Existential packaging of the concrete scan/collapse split.  The witness
data remains inside `Prop`, so the certificate can be constructed directly
from the existential safety theorems without adding a choice axiom. -/
def PolicyTraceReplaySplit
    (input : RunSpan) (initialForest : List SpannedMergeTree)
    (execution : TraceResult (ListSortImplResult κ ν)) : Prop :=
  ∃ (openState : MergeState κ ν)
    (openForest closedForest : List SpannedMergeTree)
    (scanEvents collapseEvents : List PolicyEvent)
    (collapsed : MergeForceCollapseResult κ ν),
    ListSortScanPolicyReplayWitness input initialForest execution openState
      openForest closedForest scanEvents collapseEvents collapsed

/-- Specialization of the generic trace split to one real scan call. -/
def ListSortScanPolicyReplayPost
    (input : RunSpan) (initialForest : List SpannedMergeTree)
    (fuel : Nat) (state : MergeState κ ν) (lo remaining : Nat)
    (reverse : Bool) (inputSize : Nat) : Prop :=
  PolicyTraceReplaySplit input initialForest
    (listSortScanTraced? fuel state lo remaining reverse inputSize)

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
