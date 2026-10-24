/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.MergeAtSafety
import Lemma.List.Atlas.CPythonListsort.Code.Policy.FoundNewRunPreservation

/-!
# `found_new_run` safety

This module traces the pending-stack reads, the delegated `merge_at` calls,
and the final top-power write performed by `found_new_run`.  Power computation
has no indexed-memory event of its own.  Exhausting either explicit bound is
recorded in the trace, while the public theorem proves that source-admitted
executions never take either exhaustion branch.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

private def foundNewRunSuccessResult (state : MergeState κ ν) :
    FoundNewRunResult κ ν :=
  { state := state, returnCode := 0, fuelExhausted := false }

private def foundNewRunOutOfFuelResult (state : MergeState κ ν) :
    FoundNewRunResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := true }

private def foundNewRunFromMergeAt (result : MergeAtResult κ ν) :
    FoundNewRunResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

/-- Trace the single C field write which initializes the current top run's
power.  Constructing the replacement record does not add a synthetic read. -/
def setTopPowerTraced? (state : MergeState κ ν) (power : Nat) :
    TraceResult (MergeState κ ν) :=
  if state.pending.isEmpty then
    TraceResult.failure
  else
    TraceResult.pendingRunPowerWrite? state
      (Int.ofNat (state.pending.size - 1)) power

/-- Traced collapse loop used by `foundNewRunTraced?`. -/
def foundNewRunLoopTraced? :
    Nat → MergeState κ ν → Nat → TraceResult (FoundNewRunResult κ ν)
  | 0, state, _ =>
      (TraceResult.pure (foundNewRunOutOfFuelResult state)).markFuelExhausted
  | fuel + 1, state, power =>
      if 1 < state.pending.size then
        (TraceResult.pendingRunRead? state
          (Int.ofNat (state.pending.size - 2))).bind fun preceding =>
            match preceding.power with
            | none => TraceResult.failure
            | some precedingPower =>
                if power < precedingPower then
                  (mergeAtTraced? state (state.pending.size - 2)).bind fun merged =>
                    if merged.returnCode = 0 ∧ !merged.fuelExhausted then
                      foundNewRunLoopTraced? fuel merged.state power
                    else
                      TraceResult.pure (foundNewRunFromMergeAt merged)
                else
                  (setTopPowerTraced? state power).map foundNewRunSuccessResult
      else
        (setTopPowerTraced? state power).map foundNewRunSuccessResult

/-- Fully traced `found_new_run` evaluator. -/
def foundNewRunTraced? (state : MergeState κ ν) (n2 : Nat) :
    TraceResult (FoundNewRunResult κ ν) :=
  if state.pending.isEmpty then
    TraceResult.pure (foundNewRunSuccessResult state)
  else
    (TraceResult.pendingRunRead? state
      (Int.ofNat (state.pending.size - 1))).bind fun top =>
        if (!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
            (0 : PySSize).slt top.len && decide (0 < n2) &&
            decide (n2 ≤ PY_SSIZE_T_MAX) &&
            decide (top.base - state.basekeys + top.len.toNat + n2 ≤
              state.listlen.toNat) then
          let powered := powerloopTraced
            (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
            (BitVec.ofNat 64 n2) state.listlen
          if !powered.stopped then
            (TraceResult.pure
              (foundNewRunOutOfFuelResult state)).markFuelExhausted
          else
            foundNewRunLoopTraced? state.pending.size state powered.result
        else
          TraceResult.failure

/-- State fields which `found_new_run` is not allowed to change. -/
structure FoundNewRunStableFrame (before after : MergeState κ ν) : Prop where
  listlen : after.listlen = before.listlen
  basekeys : after.basekeys = before.basekeys
  dataSize : after.data.entries.size = before.data.entries.size
  tempValuesMode : after.a.hasValues = before.a.hasValues
  comparator : after.key_compare = before.key_compare
  mrCurrent : after.mr_current = before.mr_current
  mrE : after.mr_e = before.mr_e
  mrMask : after.mr_mask = before.mr_mask

namespace FoundNewRunStableFrame

private structure SetTopPowerSafetyPost (before : MergeState κ ν)
    (power : Nat) (after : MergeState κ ν) : Prop where
  resultEq : (setTopPowerTraced? before power).result = some after
  traceSafe : MovementTraceSafe (setTopPowerTraced? before power)
  exactErasure : (setTopPowerTraced? before power).erase =
    setTopPower? before power
  stableFrame : FoundNewRunStableFrame before after
  storageEq : after.a = before.a
  allocedEq : after.alloced = before.alloced
  dataEq : after.data = before.data
  pendingSize : after.pending.size = before.pending.size

private structure FoundNewRunLoopSafetyPost
    (pre : MergeState κ ν) (scanned fuel power : Nat)
    (result : FoundNewRunResult κ ν) : Prop where
  resultEq : (foundNewRunLoopTraced? fuel pre power).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafe : MovementTraceSafe (foundNewRunLoopTraced? fuel pre power)
  exactErasure : (foundNewRunLoopTraced? fuel pre power).erase =
    foundNewRunLoop? fuel pre power
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  hasValuesFrame : result.state.a.hasValues = pre.a.hasValues
  stableFrame : FoundNewRunStableFrame pre result.state
  memoryEventsValid :
    (foundNewRunLoopTraced? fuel pre power).trace.memoryEventsValid
      pre.a.hasValues
  onlyMergeMemoryEvents :
    (foundNewRunLoopTraced? fuel pre power).trace.onlyMergeMemoryEvents
  memoryEventsBounded :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (foundNewRunLoopTraced? fuel pre power).trace.mergeMemoryEventsBounded
  physicalSlotsBound :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (MergeMemorySnapshot.ofState result.state).PhysicalBound
  memorySegment :
    (foundNewRunLoopTraced? fuel pre power).trace.MergeMemorySegment
      (MergeMemorySnapshot.ofState pre)
      (MergeMemorySnapshot.ofState result.state)

/-- End-to-end safety certificate for one admitted `found_new_run` call. -/
structure FoundNewRunSafetyPost (pre : MergeState κ ν) (scanned : Nat)
    (newRun : PendingRun) (result : FoundNewRunResult κ ν) : Prop where
  resultEq :
    (foundNewRunTraced? pre newRun.len.toNat).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceFuel :
    (foundNewRunTraced? pre newRun.len.toNat).trace.fuelExhausted = false
  accessesInBounds :
    (foundNewRunTraced? pre newRun.len.toNat).trace.allAccessesInBounds
  tempAccessesLive :
    (foundNewRunTraced? pre newRun.len.toNat).trace.tempPayloadAccessesLive
  noPushes :
    (foundNewRunTraced? pre newRun.len.toNat).trace.pushDepths = []
  exactErasure :
    (foundNewRunTraced? pre newRun.len.toNat).erase =
      foundNewRun? pre newRun.len.toNat
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  hasValuesFrame : result.state.a.hasValues = pre.a.hasValues
  stableFrame : FoundNewRunStableFrame pre result.state
  memoryEventsValid :
    (foundNewRunTraced? pre newRun.len.toNat).trace.memoryEventsValid
      pre.a.hasValues
  onlyMergeMemoryEvents :
    (foundNewRunTraced? pre newRun.len.toNat).trace.onlyMergeMemoryEvents
  memoryEventsBounded :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (foundNewRunTraced? pre newRun.len.toNat).trace.mergeMemoryEventsBounded
  physicalSlotsBound :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (MergeMemorySnapshot.ofState result.state).PhysicalBound
  memorySegment :
    (foundNewRunTraced? pre newRun.len.toNat).trace.MergeMemorySegment
      (MergeMemorySnapshot.ofState pre)
      (MergeMemorySnapshot.ofState result.state)
  readyToPush : ReadyToPush result.state scanned newRun

private def foundNewRunUnpoweredOlder : PendingRun :=
  { base := 0, len := 1, power := none }

private def foundNewRunUnpoweredNewest : PendingRun :=
  { base := 1, len := 1, power := none }

private def foundNewRunUnpoweredRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 1, value := none },
            { key := 2, value := none },
            { key := 3, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending := #[foundNewRunUnpoweredOlder, foundNewRunUnpoweredNewest]
    key_compare := fun _ _ => false
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }
