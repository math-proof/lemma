/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemcpyProvenance.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.MergeLo.Part6
import Def.CPythonListsort.Code.Transcription.MergeHi.Part6
import Lean.Elab.Command
import Theorem.CPythonListsort.Code.Assembly.MergeMemcpyProvenance
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

/-! ## Closed bulk-movement inventory -/

/-- The primitive class used at a merge bulk-movement site. -/
inductive MergeBulkMoveKind where
  | distinctBackingMemcpy
  | sameStoreMemmove
  deriving DecidableEq, Repr

/-- Type-level vocabulary for the six temp/main `memcpy` tags and four
same-main-store `memmove` tags.  Actual evaluator coverage is checked against
declaration bodies below; constructor counting is not used as coverage proof. -/
inductive MergeBulkMoveCallsite where
  | loMemcpy (site : MergeLoMemcpyCallsite)
  | hiMemcpy (site : MergeHiMemcpyCallsite)
  | memmove (site : MergeMemmoveCallsite)
  deriving DecidableEq, Repr

end CPythonListsort
