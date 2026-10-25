/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Structure.CPythonListsort.Code.Assembly.MergeHiSafety.Part3
/-!
# `merge_hi` traced execution and safety

This module instruments the right-to-left merge directly.  Its evaluator does
not run `mergeHi?` and attach a second, decorative trace: every state transition
is produced by the typed operation that emits its access events.  The three
`memcpy` paths retain their exact source call-site tag and distinct-backing
permit, main-data block movement uses the overlap-safe traced `memmove`, and
temporary gallops read their live storage through `GallopKeySource.temporary`.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace MergeHiStableFrame

namespace MergeHiStorageFrame

namespace MergeHiCursorInvariant

/-! ## Staged proof of the public contract -/

/-- Cursor immediately before CPython's forced first copy from the left run. -/
def mergeHiFullCursor (call : MergeAtCall κ ν)
    (copied : MergeState κ ν) : MergeHiCursor κ ν :=
  { state := copied
    dest := call.ssb + Int.ofNat (call.nb - 1)
    ssa := call.ssa + Int.ofNat (call.na - 1)
    ssb := Int.ofNat (call.nb - 1)
    basea := call.ssa
    na := call.na
    nb := call.nb
    minGallop := copied.min_gallop
    phase := .straight 0 0 }

/-- Cursor passed to the recursive phase machine after the forced first copy. -/
def mergeHiInitialCursor (call : MergeAtCall κ ν)
    (forced : MergeHiDataCursorResult κ ν) : MergeHiCursor κ ν :=
  { state := forced.state
    dest := forced.dst
    ssa := forced.src
    ssb := Int.ofNat (call.nb - 1)
    basea := call.ssa
    na := call.na - 1
    nb := call.nb
    minGallop := forced.state.min_gallop
    phase := .straight 0 0 }

/-- Traced continuation following the forced first copy. -/
def mergeHiTracedTail (call : MergeAtCall κ ν)
    (item : MergeHiDataCursorResult κ ν) : TraceResult (MergeHiResult κ ν) :=
  mergeHiLoopTraced? (call.na + call.nb) (mergeHiInitialCursor call item)

/-- Reviewed untraced continuation corresponding to `mergeHiTracedTail`. -/
def mergeHiReferenceTail (call : MergeAtCall κ ν)
    (item : MergeHiDataCursorResult κ ν) : Option (MergeHiResult κ ν) :=
  mergeHiLoop? (call.na + call.nb) (mergeHiInitialCursor call item)

/-- Traced entry continuation following the initial main-to-temporary copy. -/
def mergeHiTracedAfterCopy (call : MergeAtCall κ ν)
    (state : MergeState κ ν) : TraceResult (MergeHiResult κ ν) :=
  (mergeHiCopyDataDecrTraced? state
    (call.ssb + Int.ofNat (call.nb - 1))
    (call.ssa + Int.ofNat (call.na - 1))).bind (mergeHiTracedTail call)

/-- Untraced entry continuation corresponding to `mergeHiTracedAfterCopy`. -/
def mergeHiReferenceAfterCopy (call : MergeAtCall κ ν)
    (state : MergeState κ ν) : Option (MergeHiResult κ ν) :=
  (mergeHiCopyDataDecr? state
    (call.ssb + Int.ofNat (call.nb - 1))
    (call.ssa + Int.ofNat (call.na - 1))).bind (mergeHiReferenceTail call)

end MergeHiCursorInvariant
end MergeHiStorageFrame
end MergeHiStableFrame
end CPythonListsort
