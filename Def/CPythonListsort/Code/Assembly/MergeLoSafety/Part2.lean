/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Structure.CPythonListsort.Code.Assembly.MergeLoSafety
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
