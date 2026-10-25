/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Def.CPythonListsort.Code.Assembly.MergeLoSafety.Part4
/-!
# `merge_lo` lockstep safety

This module instruments the reviewed `merge_lo` transcription with the typed
main-data and temporary-storage primitives from `MergeTracePrimitives`.
Temporary gallops read their actual temporary backing directly; the
materialized `SortSlice` is used only as an untraced semantic bridge to the
reviewed evaluator.
-/


namespace CPythonListsort

universe u v w

variable {κ : Type u} {ν : Type v}

namespace MergeLoStableFrame

namespace MergeLoStorageFrame

namespace MergeLoMachineInvariant

/-- Output of the call-site/allocation/initial-copy stage.  It packages the
facts later stages actually consume, including the invariant of the exact
machine installed by the transcription. -/
structure MergeLoInitialStage
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (copied : MergeState κ ν) : Prop where
  requestFacts : MergeGetmemRequestBoundFacts pre scanned i call.na call
  geometry : MergeAtSafetyGeometry pre scanned i call
  inputTempInvariant : TempStorageInv call.state.a call.state.alloced
  inputTempLive : call.state.a.Live
  inputValuesMode :
    SortSlice.ValuesModeInvariant call.state.a.hasValues call.state.data
  allocationPost : MergeGetmemStoragePost call.state
    (BitVec.ofNat 64 call.na) (mergeLoAllocated call)
  copyPost : MainToTempMemcpyPost (.lo .initialDataToTemp)
    mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state copied
    0 call.ssa
  initialInvariant : MergeLoMachineInvariant (mergeLoAllocated call).state call.na
    (mergeLoEndIndex call) (mergeLoInitialMachine call copied)

/-- Output of the initial `B` move plus the complete lockstep tail. -/
structure MergeLoCoreStage (call : MergeAtCall κ ν)
    (copied : MergeState κ ν) (result : MergeLoResult κ ν) : Prop where
  corePost : MergeLoCorePost (mergeLoAllocated call).state call.na
    (mergeLoTracedAfterCopy call copied)
    (mergeLoReferenceAfterCopy call copied) result
  tempRead : (mergeLoTracedAfterCopy call copied).trace.HasTempAccess .read

end MergeLoMachineInvariant
end MergeLoStorageFrame
end MergeLoStableFrame
end CPythonListsort
