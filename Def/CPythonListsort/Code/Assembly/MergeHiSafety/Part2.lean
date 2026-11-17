/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean -/

module

public import Structure.CPythonListsort.Code.Assembly.MergeHiSafety

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

/-- The outer fuel stays strictly ahead of the number of unmerged entries.
That one-step slack is created by the forced initial left copy. -/
def MergeHiFuelInvariant (fuel : Nat) (cursor : MergeHiCursor κ ν) : Prop :=
  cursor.na + cursor.nb < fuel

end MergeHiStorageFrame
end MergeHiStableFrame
end CPythonListsort
