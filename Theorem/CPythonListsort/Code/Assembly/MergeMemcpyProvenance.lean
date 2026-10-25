/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemcpyProvenance.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.MergeLo.Part6
import Def.CPythonListsort.Code.Transcription.MergeHi.Part6
import Lean.Elab.Command
import Structure.CPythonListsort.Code.Assembly.MergeMemcpyProvenance
/-!
# Merge memcpy call-site provenance

The generic `sortslice_memcpy` model must reject an overlapping request on one
backing, while CPython's six bulk-copy sites inside `merge_lo` and `merge_hi`
are admissible because they cross between the main list and temporary storage.
This module makes that call-site fact an exported assembly obligation rather
than leaving it implicit in the two C pointers.  The transcriptions enforce
the obligation structurally: their recursive bulk-copy executors themselves
require a call-site tag and a proof of its exact backing direction, with no
lower untagged bulk helper for an evaluator call to bypass.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

open SortSlice

/-- The exact `merge_lo`/`merge_hi` memcpy sites satisfy distinct-backing
provenance, while the generic same-backing overlap case remains rejected.

This is the declaration intended for the roadmap node's `lean:` field. -/
theorem mergeMemcpyCallsiteProvenance :
    MergeMemcpyCallsiteProvenanceContract κ ν where
  mergeLoCallsitesDistinct := mergeLo_memcpyCallsite_distinct
  mergeHiCallsitesDistinct := mergeHi_memcpyCallsite_distinct
  distinctBackingAdmissible := by
    intro destination source dst src count
    trivial
  sameBackingOverlapRejected := memcpyTraced_sameBacking_overlap_rejected

end CPythonListsort
