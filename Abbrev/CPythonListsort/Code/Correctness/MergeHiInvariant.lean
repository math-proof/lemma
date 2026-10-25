/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeHiInvariant.lean -/

import Def.CPythonListsort.Code.Assembly.GallopCorrectness
import Theorem.CPythonListsort.Code.Assembly.MergeHiSafety.Part5
import Def.CPythonListsort.Code.Correctness.MergeMovementCorrectness.Part2
import Structure.CPythonListsort.Code.Correctness.MergeSemanticPre
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Def.CPythonListsort.Code.Correctness.StableMerge
import Def.CPythonListsort.Code.Correctness.MergeHiInvariant
/-!
# Semantic invariant for `merge_hi`

The safety invariant for `merge_hi` deliberately records only cursor geometry,
storage validity, and stable state fields.  Functional correctness needs a
separate immutable snapshot of the two post-trimming runs and a description of
the suffix already filled by the right-to-left loop.  This module introduces
that semantic vocabulary without changing the reviewed safety certificate.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- `merge_hi` consumes exactly the shared post-trimming semantic contract.
The direction-specific name is retained as an abbreviation so downstream
statements remain readable while both merge directions are definitionally
obligated to the same predicate shape. -/
abbrev MergeHiSemanticPre
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu) : Prop :=
  MergeSemanticPre lt call

end CPythonListsort
