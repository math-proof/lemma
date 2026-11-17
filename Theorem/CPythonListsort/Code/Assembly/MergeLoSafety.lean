/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean -/

module

public import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
public import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
public import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
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

/-! ## Classified bulk-copy permits -/

/-- Provenance permit consumed by the initial main-to-temporary copy. -/
public theorem mergeLoInitialDataToTempPermit :
    (MergeMemcpySite.lo .initialDataToTemp).MainToTempPermit where
  direction := rfl
  distinctBacking := MergeMemcpySite.distinct _

/-- Provenance permit consumed by an A-side gallop block copy. -/
public theorem mergeLoGallopTempToDataPermit :
    (MergeMemcpySite.lo .gallopTempToData).TempToMainPermit where
  direction := rfl
  distinctBacking := MergeMemcpySite.distinct _

/-- Provenance permit consumed by the final A-side remainder copy. -/
public theorem mergeLoFinalTempToDataPermit :
    (MergeMemcpySite.lo .finalTempToData).TempToMainPermit where
  direction := rfl
  distinctBacking := MergeMemcpySite.distinct _

end CPythonListsort
