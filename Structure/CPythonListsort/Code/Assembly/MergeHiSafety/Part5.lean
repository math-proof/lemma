/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean -/

module

public import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
public import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
public import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
public import Structure.CPythonListsort.Code.Assembly.MergeHiSafety.Part2
public import Structure.CPythonListsort.Code.Assembly.MergeMemcpyProvenance
public import Def.CPythonListsort.Code.Transcription.MergeHi.Part5
public import Structure.CPythonListsort.Code.Transcription.MergeHi.Part2
public import Def.CPythonListsort.Code.Assembly.MergeHiSafety.Part4
public import Def.CPythonListsort.Code.Assembly.MergeHiSafety
public import Def.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part4
/-!
# `merge_hi` traced execution and safety

This module instruments the right-to-left merge directly.  Its evaluator does
not run `mergeHi?` and attach a second, decorative trace: every state transition
is produced by the typed operation that emits its access events.  The three
`memcpy` paths retain their exact source call-site tag and distinct-backing
permit, main-data block movement uses the overlap-safe traced `memmove`, and
temporary gallops read their live storage through `GallopKeySource.temporary`.
-/
public section




namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace MergeHiStableFrame

namespace MergeHiStorageFrame

namespace MergeHiCursorInvariant

/-- Observable evidence separated from the recursive lockstep proof.  These
witnesses rule out a vacuous safety result: the successful merge really reads
the input, writes and later reads temporary storage, and preserves the
classified-`memcpy` provenance boundary. -/
structure MergeHiObservablePost
    (call : MergeAtCall κ ν) (result : MergeHiResult κ ν) : Prop where
  core : MergeHiCorePost (mergeHiAllocated call).state call.nb
    (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb)
    (mergeHi? call.state call.ssa call.ssb call.na call.nb) result
  memcpyProvenance : MergeMemcpyCallsiteProvenanceContract κ ν
  inputKeyEvent :
    (mergeHiTraced? call.state call.ssa call.ssb call.na
      call.nb).trace.HasAccess .read .inputKeys
  tempWriteEvent :
    (mergeHiTraced? call.state call.ssa call.ssb call.na
      call.nb).trace.HasTempAccess .write
  tempReadEvent :
    (mergeHiTraced? call.state call.ssa call.ssb call.na
      call.nb).trace.HasTempAccess .read
  synchronizedValuesEvent : call.state.a.hasValues = true →
    (mergeHiTraced? call.state call.ssa call.ssb call.na
      call.nb).trace.HasAccess .read .synchronizedValues

end MergeHiCursorInvariant
end MergeHiStorageFrame
end MergeHiStableFrame
end CPythonListsort
