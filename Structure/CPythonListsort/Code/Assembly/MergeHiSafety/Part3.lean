/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Def.CPythonListsort.Code.Assembly.MergeHiSafety.Part4
/-!
# `merge_hi` traced execution and safety

This module instruments the right-to-left merge directly.  Its evaluator does
not run `mergeHi?` and attach a second, decorative trace: every state transition
is produced by the typed operation that emits its access events.  The three
`memcpy` paths retain their exact source call-site tag and distinct-backing
permit, main-data block movement uses the overlap-safe traced `memmove`, and
temporary gallops read their live storage through `GallopKeySource.temporary`.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace MergeHiStableFrame

namespace MergeHiStorageFrame

namespace MergeHiCursorInvariant

/-- Full externally consumable postcondition for an actual `merge_at`
`merge_hi` continuation. -/
structure MergeHiSafetyPost
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (execution : TraceResult (MergeHiResult κ ν))
    (result : MergeHiResult κ ν) : Prop where
  resultEq : execution.result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceFuel : execution.trace.fuelExhausted = false
  accessesInBounds : execution.trace.allAccessesInBounds
  tempAccessesLive : execution.trace.tempPayloadAccessesLive
  noPushes : execution.trace.pushDepths = []
  noMemoryEvents : execution.trace.memoryEvents = []
  exactErasure : execution.erase =
    mergeHi? call.state call.ssa call.ssb call.na call.nb
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  logicalCapacity : result.state.a.cells.size = result.state.alloced.toNat
  requestFits : call.nb ≤ result.state.alloced.toNat
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  stableFrame : MergeHiStableFrame call.state result.state
  geometry : MergeAtSafetyGeometry pre scanned i call
  requestFacts : MergeGetmemRequestBoundFacts pre scanned i call.nb call
  inputTempInvariant : TempStorageInv call.state.a call.state.alloced
  inputTempLive : call.state.a.Live
  inputValuesMode :
    SortSlice.ValuesModeInvariant call.state.a.hasValues call.state.data
  directionalDispatch : call.nb < call.na
  /-- Exact allocation certificate for the `merge_getmem` result consumed by
  the directional merge. -/
  allocationPost : MergeGetmemStoragePost call.state
    (BitVec.ofNat 64 call.nb) (mergeHiAllocated call)
  /-- Exact temporary-storage metadata frame from post-`merge_getmem` through
  the final right-to-left merge state. -/
  postGetmemStorageFrame :
    MergeHiStorageFrame (mergeHiAllocated call).state result.state
  /-- Reuse transports a caller-supplied physical-slot bound, while growth
  establishes it from the allocation guard. -/
  physicalSlotsBound :
    call.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES →
      result.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES
  memcpyProvenance : MergeMemcpyCallsiteProvenanceContract κ ν
  inputKeyEvent : execution.trace.HasAccess .read .inputKeys
  tempWriteEvent : execution.trace.HasTempAccess .write
  tempReadEvent : execution.trace.HasTempAccess .read
  synchronizedValuesEvent : call.state.a.hasValues = true →
    execution.trace.HasAccess .read .synchronizedValues

end MergeHiCursorInvariant
end MergeHiStorageFrame
end MergeHiStableFrame
end CPythonListsort
