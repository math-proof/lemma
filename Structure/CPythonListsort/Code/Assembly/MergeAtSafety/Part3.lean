/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeAtSafety.lean -/

import Def.CPythonListsort.Code.Assembly.MergeMemoryLifecycle.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeAtPreservation
import Def.CPythonListsort.Code.Assembly.MergeAtSafety.Part3
/-!
# `merge_at` safety

This module instruments the pending-stack updates and the two trimming gallops
performed by `merge_at`, then delegates the selected merge continuation to the
already traced `merge_lo` or `merge_hi` evaluator.  The logical shrink of the
active pending array is not an indexed C access; the indexed reads and writes
which precede it are recorded in source order.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace MergeAtStableFrame

/-- Full public postcondition for a source-admitted `merge_at` call. -/
structure MergeAtSafetyPost (pre : MergeState κ ν) (scanned i : Nat)
    (execution : TraceResult (MergeAtResult κ ν))
    (result : MergeAtResult κ ν) : Prop where
  resultEq : execution.result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceFuel : execution.trace.fuelExhausted = false
  accessesInBounds : execution.trace.allAccessesInBounds
  tempAccessesLive : execution.trace.tempPayloadAccessesLive
  noPushes : execution.trace.pushDepths = []
  /-- Every raw lifecycle observation emitted by this `merge_at` invocation is
  validated in the values mode inherited from its caller. -/
  memoryEventsValid : execution.trace.memoryEventsValid pre.a.hasValues
  /-- `merge_at` owns directional call records only; initialization and final
  cleanup remain top-level events. -/
  onlyMergeMemoryEvents : execution.trace.onlyMergeMemoryEvents
  /-- The initialized physical-slot ceiling is threaded through every call
  record rather than reconstructed from raw observations. -/
  memoryEventsBounded :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      execution.trace.mergeMemoryEventsBounded
  /-- Exact local event cardinality: an early trimmed exit emits nothing and a
  completed directional merge emits exactly its one call record. -/
  memoryEventShape :
    execution.trace.memoryEvents = [] ∨
      ∃ call, execution.trace.memoryEvents = [.mergeCall call]
  /-- The call records are not merely well-shaped: their concrete storage
  boundaries form one gap-free path from the caller state to the result. -/
  memorySegment : execution.trace.MergeMemorySegment
    (MergeMemorySnapshot.ofState pre)
    (MergeMemorySnapshot.ofState result.state)
  exactErasure : execution.erase = mergeAt? pre i
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  hasValuesFrame : result.state.a.hasValues = pre.a.hasValues
  stableFrame : MergeAtStableFrame pre result.state
  pendingLayout : PendingLayout result.state scanned
  /-- The successful full call emits exactly one logical merge event for the
  two selected adjacent runs as they stood before trimming, and the result
  pending array is exactly their source-level splice. -/
  logicalMerge : ∃ left right,
    pre.pending[i]? = some left ∧
      pre.pending[i + 1]? = some right ∧
      result.state.pending =
        (pre.pending.setIfInBounds i
          { left with len := left.len + right.len }).eraseIdxIfInBounds
            (i + 1) ∧
      execution.trace.policyEvents =
        [.merge
          { index := i
            left := RunSpan.ofPendingRun left
            right := RunSpan.ofPendingRun right }]
  physicalSlotsBound :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (MergeMemorySnapshot.ofState result.state).PhysicalBound

end MergeAtStableFrame
end CPythonListsort
