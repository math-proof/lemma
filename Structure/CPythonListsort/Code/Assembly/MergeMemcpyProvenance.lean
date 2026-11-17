/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemcpyProvenance.lean -/

module

public import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
public import Def.CPythonListsort.Code.Transcription.MergeLo.Part6
public import Def.CPythonListsort.Code.Transcription.MergeHi.Part6
public import Lean.Elab.Command
public import Def.CPythonListsort.Code.Transcription.MergeLo.Part3
public import Def.CPythonListsort.Code.Transcription.MergeHi.Part2
public import Def.CPythonListsort.Code.Assembly.SortSliceSafety
public import Def.CPythonListsort.Code.Transcription.SortSlice.Part2
public import Def.CPythonListsort.Code.Transcription.SortSlice.Part3
public import Def.CPythonListsort.Code.Transcription.SortSlice.Part4
public import Inductive.CPythonListsort.Code.Transcription.SortSlice
public import Def.CPythonListsort.Code.Assembly.AccessTrace.Part5
public import Def.CPythonListsort.Code.Assembly.AccessTrace.Part8
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
public section




namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

open SortSlice

/-- Assembly contract connecting the exact merge memcpy call sites to the
provenance-sensitive `SortSlice` safety boundary. -/
structure MergeMemcpyCallsiteProvenanceContract
    (κ : Type u) (ν : Type v) : Prop where
  /-- All three pinned `merge_lo` sites cross main and temporary storage. -/
  mergeLoCallsitesDistinct : ∀ site : MergeLoMemcpyCallsite,
    site.backings.Distinct
  /-- All three pinned `merge_hi` sites cross main and temporary storage. -/
  mergeHiCallsitesDistinct : ∀ site : MergeHiMemcpyCallsite,
    site.backings.Distinct
  /-- Explicit distinct-backing provenance discharges memcpy's aliasing
  precondition independently of indices, length, or extensional contents. -/
  distinctBackingAdmissible : ∀ (destination source : SortSlice κ ν)
      (dst src : Int) (count : Nat),
    (MemcpySource.distinctBacking source : MemcpySource destination).Admissible
      dst src count
  /-- Regression on the rejected shape: overlapping same-backing memcpy does
  not execute, emit a partial trace, or disagree with the transcription. -/
  sameBackingOverlapRejected : ∀ (valuesPresent : Bool) (count : Nat)
      (destination : SortSlice κ ν) (dst src : Int),
    ¬ MemcpyRangesDisjoint dst src count →
      (memcpyTraced? valuesPresent count destination .sameBacking dst src).result =
          none ∧
        (memcpyTraced? valuesPresent count destination .sameBacking dst src).trace =
          AccessTrace.empty ∧
        (memcpyTraced? valuesPresent count destination .sameBacking dst src).erase =
          memcpy? count destination .sameBacking dst src

end CPythonListsort
