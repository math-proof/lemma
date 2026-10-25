/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTermination.lean -/

import Def.CPythonListsort.Code.Assembly.ListSortTrace
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.TopLevelErasureForceCollapse
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.TopLevelErasureFound
/-!
# Top-level listsort termination and safety

This module carries the reviewed local safety certificates through the actual
traced `list_sort_impl` control flow.  The recursive proof is private; public
consumers see compact raw and proof-carrying entry-point certificates.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-! ## Trace composition -/

/-- The four whole-trace facts accumulated by the top-level induction. -/
structure ListSortTraceSafety (execution : TraceResult α) : Prop where
  fuel : execution.trace.fuelExhausted = false
  accessesInBounds : execution.trace.allAccessesInBounds
  tempAccessesLive : execution.trace.tempPayloadAccessesLive
  stackDepth : execution.trace.stackDepthMax ≤ 61

namespace ListSortTraceSafety

/-! ## Final cleanup -/

structure FinishListSortSuccessPost (state : MergeState κ ν)
    (reverse : Bool) (inputSize : Nat) (result : ListSortImplResult κ ν) :
    Prop where
  resultEq :
    (finishListSortTraced? state reverse inputSize 0 false).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafety :
    ListSortTraceSafety
      (finishListSortTraced? state reverse inputSize 0 false)
  memoryEventsValid :
    (finishListSortTraced? state reverse inputSize 0 false).trace.memoryEventsValid
      state.a.hasValues
  memoryEventsBounded :
    (finishListSortTraced? state reverse inputSize 0 false).trace.mergeMemoryEventsBounded
  memoryTail :
    (finishListSortTraced? state reverse inputSize 0 false).trace.MergeMemoryTail
      (MergeMemorySnapshot.ofState state)
      (MergeMemorySnapshot.ofState result.state)
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  hasValuesFrame : result.state.a.hasValues = state.a.hasValues
  finalPhysicalBound :
    (MergeMemorySnapshot.ofState result.state).PhysicalBound

/-! ## Scan invariant and certificates -/

/-- State carried at every call of the run-discovery scan.  The adaptive
minrun generator is required only while unscanned input remains: the clipped
last target is allowed to consume the suffix and enter final collapse without
manufacturing a nonexistent next active generator state. -/
structure ListSortScanInvariant (lt : BoolComparator κ) (hasKeyfunc : Bool)
    (inputSize : Nat) (state : MergeState κ ν) (lo scanned remaining : Nat) :
    Prop where
  inputSizeLower : 2 ≤ inputSize
  inputSizeMax : inputSize ≤ PY_LIST_MAX
  listlen : state.listlen.toNat = inputSize
  listlenNonnegative : state.listlen.Nonnegative
  basekeys : state.basekeys = 0
  dataExtent : state.data.entries.size = inputSize
  cursor : lo = state.basekeys + scanned
  partition : scanned + remaining = inputSize
  pendingLayout : PendingLayout state scanned
  poweredPrefix : PoweredPrefix state
  tempInvariant : TempStorageInv state.a state.alloced
  tempLive : state.a.Live
  physicalSlotsBound :
    (MergeMemorySnapshot.ofState state).PhysicalBound
  hasValues : state.a.hasValues = hasKeyfunc
  valuesMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data
  comparator : state.key_compare = lt
  adaptive : 0 < remaining →
    ∃ calls, AdaptiveMinrunScanInvariant state.listlen calls scanned
      state.minrunState

/-- Successful top-level scan result, including the exact raw erasure and all
trace properties accumulated from the real helper sequence. -/
structure ListSortScanSafetyPost (fuel : Nat) (state : MergeState κ ν)
    (lo remaining : Nat) (reverse : Bool) (inputSize : Nat)
    (result : ListSortImplResult κ ν) : Prop where
  resultEq :
    (listSortScanTraced? fuel state lo remaining reverse inputSize).result =
      some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafety :
    ListSortTraceSafety
      (listSortScanTraced? fuel state lo remaining reverse inputSize)
  memoryEventsValid :
    (listSortScanTraced? fuel state lo remaining reverse inputSize).trace.memoryEventsValid
      state.a.hasValues
  memoryEventsBounded :
    (listSortScanTraced? fuel state lo remaining reverse inputSize).trace.mergeMemoryEventsBounded
  memoryTail :
    (listSortScanTraced? fuel state lo remaining reverse inputSize).trace.MergeMemoryTail
      (MergeMemorySnapshot.ofState state)
      (MergeMemorySnapshot.ofState result.state)
  exactErasure :
    (listSortScanTraced? fuel state lo remaining reverse inputSize).erase =
      listSortScan? fuel state lo remaining reverse inputSize
  finalTempInvariant : TempStorageInv result.state.a result.state.alloced
  finalValuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  finalHasValues : result.state.a.hasValues = state.a.hasValues
  finalPhysicalBound :
    (MergeMemorySnapshot.ofState result.state).PhysicalBound

/-- Raw `list_sort_impl` adequacy and whole-trace safety certificate. -/
structure ListSortImplSafetyPost (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν) (result : ListSortImplResult κ ν) : Prop where
  resultEq :
    (listSortImplTraced? lt reverse hasKeyfunc input).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafety :
    ListSortTraceSafety (listSortImplTraced? lt reverse hasKeyfunc input)
  memoryLifecycle :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.MergeMemoryLifecycle
      hasKeyfunc
      (MergeMemorySnapshot.ofState
        (initialMergeState lt hasKeyfunc input).1)
      (MergeMemorySnapshot.ofState result.state)
  exactErasure :
    (listSortImplTraced? lt reverse hasKeyfunc input).erase =
      listSortImpl? lt reverse hasKeyfunc input
  finalTempInvariant : TempStorageInv result.state.a result.state.alloced
  finalValuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  finalHasValues : result.state.a.hasValues = hasKeyfunc
  finalPhysicalBound :
    (MergeMemorySnapshot.ofState result.state).PhysicalBound

/-- Public proof-carrying wrapper certificate. -/
structure ListSortSafetyPost (lt : BoolComparator κ) (reverse : Bool)
    (input : ListSortInput κ ν) (result : ListSortImplResult κ ν) : Prop where
  resultEq : (listSortTraced? lt reverse input).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafety : ListSortTraceSafety (listSortTraced? lt reverse input)
  memoryLifecycle :
    (listSortTraced? lt reverse input).trace.MergeMemoryLifecycle
      input.hasKeyfunc
      (MergeMemorySnapshot.ofState
        (initialMergeState lt input.hasKeyfunc input.slice).1)
      (MergeMemorySnapshot.ofState result.state)
  exactErasure :
    (listSortTraced? lt reverse input).erase = listSort? lt reverse input
  finalTempInvariant : TempStorageInv result.state.a result.state.alloced
  finalValuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  finalHasValues : result.state.a.hasValues = input.hasKeyfunc
  finalPhysicalBound :
    (MergeMemorySnapshot.ofState result.state).PhysicalBound

structure ListSortExecutionPost
    (execution : TraceResult (ListSortImplResult κ ν))
    (initialHasValues : Bool) (memoryStart : MergeMemorySnapshot)
    (result : ListSortImplResult κ ν) : Prop where
  resultEq : execution.result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafety : ListSortTraceSafety execution
  memoryEventsValid : execution.trace.memoryEventsValid initialHasValues
  memoryEventsBounded : execution.trace.mergeMemoryEventsBounded
  memoryTail : execution.trace.MergeMemoryTail memoryStart
    (MergeMemorySnapshot.ofState result.state)
  finalTempInvariant : TempStorageInv result.state.a result.state.alloced
  finalValuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  finalHasValues : result.state.a.hasValues = initialHasValues
  finalPhysicalBound :
    (MergeMemorySnapshot.ofState result.state).PhysicalBound

structure ListSortImplExecutionPost
    (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν) (result : ListSortImplResult κ ν) : Prop where
  resultEq :
    (listSortImplTraced? lt reverse hasKeyfunc input).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafety :
    ListSortTraceSafety (listSortImplTraced? lt reverse hasKeyfunc input)
  memoryLifecycle :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.MergeMemoryLifecycle
      hasKeyfunc
      (MergeMemorySnapshot.ofState
        (initialMergeState lt hasKeyfunc input).1)
      (MergeMemorySnapshot.ofState result.state)
  finalTempInvariant : TempStorageInv result.state.a result.state.alloced
  finalValuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  finalHasValues : result.state.a.hasValues = hasKeyfunc
  finalPhysicalBound :
    (MergeMemorySnapshot.ofState result.state).PhysicalBound

end ListSortTraceSafety
end CPythonListsort
