/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean -/

import Def.CPythonListsort.Code.Assembly.MergeAtSafety.Part4
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeForceCollapsePreservation
import Def.CPythonListsort.Code.Assembly.MergeForceCollapseSafety
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

structure MergeForceCollapseLoopSafetyPost
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

end MergeForceCollapseStableFrame
end CPythonListsort
