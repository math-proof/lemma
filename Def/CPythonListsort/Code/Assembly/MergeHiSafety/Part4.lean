/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean -/

module

public import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
public import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
public import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2

@[expose] public section

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

/-- The allocation performed at the `merge_hi` entry.  Naming it once keeps
the allocation/copy stage and later entry-erasure stage definitionally in
sync. -/
def mergeHiAllocated (call : MergeAtCall κ ν) :
    MergeGetmemResult κ ν :=
  mergeGetmem call.state (BitVec.ofNat 64 call.nb)

end MergeHiCursorInvariant
end MergeHiStorageFrame
end MergeHiStableFrame
end CPythonListsort
