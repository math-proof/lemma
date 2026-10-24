/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.MergeAtSafety
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeForceCollapsePreservation

/-!
# `merge_force_collapse` safety

This module traces the neighboring pending-run reads performed by the reviewed
sequential Lean transcription of `merge_force_collapse` and composes them with
the complete trace of each delegated `merge_at` call.  This is an exact order
claim about the Lean model; it does not impose an evaluation order on the two
operands of C's `<` operator.  The public safety theorem proves that the
pending-depth fuel supplied by the transcription is adequate for every
nonempty valid layout.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

private def mergeForceCollapseSuccessResult (state : MergeState κ ν) :
    MergeForceCollapseResult κ ν :=
  { state := state, returnCode := 0, fuelExhausted := false }

private def mergeForceCollapseOutOfFuelResult (state : MergeState κ ν) :
    MergeForceCollapseResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := true }

private def mergeForceCollapseFromMergeAt (result : MergeAtResult κ ν) :
    MergeForceCollapseResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

/-- Traced form of the source's merge-position choice.  When there are at
least three pending runs, the reviewed sequential Lean model records the lower
neighbor and then the upper neighbor.  This is not a claim about C operand
evaluation order. -/
def forceCollapseIndexTraced? (state : MergeState κ ν) : TraceResult Nat :=
  if 1 < state.pending.size then
    let i := state.pending.size - 2
    if 0 < i then
      (TraceResult.pendingRunRead? state (Int.ofNat (i - 1))).bind fun previous =>
        (TraceResult.pendingRunRead? state (Int.ofNat (i + 1))).map fun following =>
          if previous.len.slt following.len then i - 1 else i
    else
      TraceResult.pure i
  else
    TraceResult.failure

/-- Fuel-bounded traced collapse loop.  Exhaustion is observable both in its
result and in the trace. -/
def mergeForceCollapseLoopTraced? :
    Nat → MergeState κ ν → TraceResult (MergeForceCollapseResult κ ν)
  | 0, state =>
      if state.pending.size ≤ 1 then
        TraceResult.pure (mergeForceCollapseSuccessResult state)
      else
        (TraceResult.pure
          (mergeForceCollapseOutOfFuelResult state)).markFuelExhausted
  | fuel + 1, state =>
      if 1 < state.pending.size then
        (forceCollapseIndexTraced? state).bind fun i =>
          (mergeAtTraced? state i).bind fun merged =>
            if merged.returnCode = 0 ∧ !merged.fuelExhausted then
              mergeForceCollapseLoopTraced? fuel merged.state
            else
              TraceResult.pure (mergeForceCollapseFromMergeAt merged)
      else
        TraceResult.pure (mergeForceCollapseSuccessResult state)

/-- Fully traced `merge_force_collapse` evaluator. -/
def mergeForceCollapseTraced? (state : MergeState κ ν) :
    TraceResult (MergeForceCollapseResult κ ν) :=
  mergeForceCollapseLoopTraced? state.pending.size state

/-- State fields which the collapse loop is forbidden to mutate. -/
structure MergeForceCollapseStableFrame
    (before after : MergeState κ ν) : Prop where
  listlen : after.listlen = before.listlen
  basekeys : after.basekeys = before.basekeys
  dataSize : after.data.entries.size = before.data.entries.size
  tempValuesMode : after.a.hasValues = before.a.hasValues
  comparator : after.key_compare = before.key_compare
  mrCurrent : after.mr_current = before.mr_current
  mrE : after.mr_e = before.mr_e
  mrMask : after.mr_mask = before.mr_mask

namespace MergeForceCollapseStableFrame

private structure MergeForceCollapseLoopSafetyPost
    (pre : MergeState κ ν) (scanned fuel : Nat)
    (result : MergeForceCollapseResult κ ν) : Prop where
  resultEq :
    (mergeForceCollapseLoopTraced? fuel pre).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafe : MovementTraceSafe (mergeForceCollapseLoopTraced? fuel pre)
  exactErasure :
    (mergeForceCollapseLoopTraced? fuel pre).erase =
      mergeForceCollapseLoop? fuel pre
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  hasValuesFrame : result.state.a.hasValues = pre.a.hasValues
  memoryEventsValid :
    (mergeForceCollapseLoopTraced? fuel pre).trace.memoryEventsValid
      pre.a.hasValues
  onlyMergeMemoryEvents :
    (mergeForceCollapseLoopTraced? fuel pre).trace.onlyMergeMemoryEvents
  memoryEventsBounded :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (mergeForceCollapseLoopTraced? fuel pre).trace.mergeMemoryEventsBounded
  physicalSlotsBound :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (MergeMemorySnapshot.ofState result.state).PhysicalBound
  memorySegment :
    (mergeForceCollapseLoopTraced? fuel pre).trace.MergeMemorySegment
      (MergeMemorySnapshot.ofState pre)
      (MergeMemorySnapshot.ofState result.state)
  stableFrame : MergeForceCollapseStableFrame pre result.state
  pendingLayout : PendingLayout result.state scanned
  singleton : ∃ run, result.state.pending.toList = [run]

/-- Full public postcondition for a source-admitted final collapse. -/
structure MergeForceCollapseSafetyPost
    (pre : MergeState κ ν) (scanned : Nat)
    (result : MergeForceCollapseResult κ ν) : Prop where
  resultEq : (mergeForceCollapseTraced? pre).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceFuel :
    (mergeForceCollapseTraced? pre).trace.fuelExhausted = false
  accessesInBounds :
    (mergeForceCollapseTraced? pre).trace.allAccessesInBounds
  tempAccessesLive :
    (mergeForceCollapseTraced? pre).trace.tempPayloadAccessesLive
  noPushes : (mergeForceCollapseTraced? pre).trace.pushDepths = []
  exactErasure :
    (mergeForceCollapseTraced? pre).erase = mergeForceCollapse? pre
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  hasValuesFrame : result.state.a.hasValues = pre.a.hasValues
  memoryEventsValid :
    (mergeForceCollapseTraced? pre).trace.memoryEventsValid pre.a.hasValues
  onlyMergeMemoryEvents :
    (mergeForceCollapseTraced? pre).trace.onlyMergeMemoryEvents
  memoryEventsBounded :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (mergeForceCollapseTraced? pre).trace.mergeMemoryEventsBounded
  physicalSlotsBound :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (MergeMemorySnapshot.ofState result.state).PhysicalBound
  memorySegment :
    (mergeForceCollapseTraced? pre).trace.MergeMemorySegment
      (MergeMemorySnapshot.ofState pre)
      (MergeMemorySnapshot.ofState result.state)
  stableFrame : MergeForceCollapseStableFrame pre result.state
  pendingLayout : PendingLayout result.state scanned
  singleton : ∃ run, result.state.pending.toList = [run]
  finalRun : ∃ run,
    result.state.pending.toList = [run] ∧
      run.base = pre.basekeys ∧
      run.endIndex = pre.basekeys + scanned

/-! ## Branch and failure anti-vacuity regressions -/

private def forceCollapseTwoRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 2
    basekeys := 0
    data := { entries := #[] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := none },
        { base := 1, len := 1, power := none }]
    key_compare := fun _ _ => false
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def forceCollapseEmptyRegressionState : MergeState Nat Nat :=
  { forceCollapseTwoRegressionState with pending := #[] }

private def forceCollapseLowerRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 6
    basekeys := 0
    data := { entries := #[] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := none },
        { base := 1, len := 2, power := none },
        { base := 3, len := 3, power := none }]
    key_compare := fun _ _ => false
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def forceCollapseTieRegressionState : MergeState Nat Nat :=
  { forceCollapseLowerRegressionState with
    pending :=
      #[{ base := 0, len := 1, power := none },
        { base := 1, len := 2, power := none },
        { base := 3, len := 1, power := none }] }

private def forceCollapseRejectedMergeState : MergeState Nat Nat :=
  { forceCollapseTieRegressionState with
    listlen := 0
    pending :=
      #[{ base := 0, len := 0, power := none },
        { base := 0, len := 0, power := none }] }
