/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean -/

module

public import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
public import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
public import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2

@[expose] public section

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

/-- The allocation selected by the concrete `merge_lo` call site.  Naming it
once keeps the preparation, core-execution, and final trace-witness stages in
lockstep without repeating the `merge_getmem` expression. -/
def mergeLoAllocated (call : MergeAtCall κ ν) :
    MergeGetmemResult κ ν :=
  mergeGetmem call.state (BitVec.ofNat 64 call.na)

end MergeLoMachineInvariant
end MergeLoStorageFrame
end MergeLoStableFrame
end CPythonListsort
