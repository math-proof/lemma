/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean -/

import Def.CPythonListsort.Code.Assembly.MergeAtSafety.Part4
import Lemma.List.Atlas.CPythonListsort.Code.Policy.FoundNewRunPreservation
import Def.CPythonListsort.Code.Assembly.FoundNewRunSafety
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

structure SetTopPowerSafetyPost (before : MergeState κ ν)
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

structure FoundNewRunLoopSafetyPost
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

end FoundNewRunStableFrame
end CPythonListsort
