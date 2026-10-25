/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Structure.CPythonListsort.Code.Assembly.MergeHiSafety.Part2
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

def MergeHiContinuationSafe
    (origin : MergeState κ ν) (request fuel : Nat)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) : Prop :=
  ∀ cursor,
    MergeHiCursorInvariant origin request cursor →
    MergeHiFuelInvariant fuel cursor →
    ∃ result, MergeHiCorePost origin request
      (nextTraced cursor) (next cursor) result

end MergeHiCursorInvariant
end MergeHiStorageFrame
end MergeHiStableFrame
end CPythonListsort
