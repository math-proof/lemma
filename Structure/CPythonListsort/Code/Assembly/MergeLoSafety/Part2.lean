/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean -/

module

public import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
public import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
public import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
public import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
public import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
public import Def.CPythonListsort.Code.Assembly.MergeLoSafety.Part2
/-!
# `merge_lo` lockstep safety

This module instruments the reviewed `merge_lo` transcription with the typed
main-data and temporary-storage primitives from `MergeTracePrimitives`.
Temporary gallops read their actual temporary backing directly; the
materialized `SortSlice` is used only as an untraced semantic bridge to the
reviewed evaluator.
-/
public section




namespace CPythonListsort

universe u v w

variable {κ : Type u} {ν : Type v}

namespace MergeLoStableFrame

namespace MergeLoStorageFrame

namespace MergeLoMachineInvariant

/-! ## Internal lockstep postconditions -/

/-- Postcondition threaded through the terminal helpers and the recursive
driver.  Its reference argument is the exact reviewed fragment represented by
the traced execution. -/
structure MergeLoCorePost
    (origin : MergeState κ ν) (tempTotal : Nat)
    (execution : TraceResult (MergeLoResult κ ν))
    (reference : Option (MergeLoResult κ ν))
    (result : MergeLoResult κ ν) : Prop where
  resultEq : execution.result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafe : MovementTraceSafe execution
  exactErasure : execution.erase = reference
  tempCapacity : tempTotal ≤ result.state.a.cells.size
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  stableFrame : MergeLoStableFrame origin result.state
  storageFrame : MergeLoStorageFrame origin result.state

end MergeLoMachineInvariant
end MergeLoStorageFrame
end MergeLoStableFrame
end CPythonListsort
