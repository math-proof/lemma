/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean -/

module

public import Def.CPythonListsort.Code.Assembly.MergeLoSafety

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

/-- The loop fuel stays strictly ahead of the number of unmerged cells. -/
def MergeLoFuelInvariant (fuel : Nat) (machine : MergeLoMachine κ ν) : Prop :=
  machine.na + machine.nb < fuel

end MergeLoStorageFrame
end MergeLoStableFrame
end CPythonListsort
