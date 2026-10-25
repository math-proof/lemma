/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
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

/-! ## Classified bulk-copy permits -/

/-- Provenance permit consumed by the initial main-to-temporary copy. -/
theorem mergeLoInitialDataToTempPermit :
    (MergeMemcpySite.lo .initialDataToTemp).MainToTempPermit where
  direction := rfl
  distinctBacking := MergeMemcpySite.distinct _

/-- Provenance permit consumed by an A-side gallop block copy. -/
theorem mergeLoGallopTempToDataPermit :
    (MergeMemcpySite.lo .gallopTempToData).TempToMainPermit where
  direction := rfl
  distinctBacking := MergeMemcpySite.distinct _

/-- Provenance permit consumed by the final A-side remainder copy. -/
theorem mergeLoFinalTempToDataPermit :
    (MergeMemcpySite.lo .finalTempToData).TempToMainPermit where
  direction := rfl
  distinctBacking := MergeMemcpySite.distinct _

end CPythonListsort
