/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeLoInvariant.lean -/

import Def.CPythonListsort.Code.Assembly.GallopCorrectness
import Structure.CPythonListsort.Code.Assembly.MergeLoSafety.Part4
import Structure.CPythonListsort.Code.Correctness.MergeSemanticPre
import Def.CPythonListsort.Code.Correctness.MergeMovementCorrectness.Part2
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Def.CPythonListsort.Code.Correctness.StableMerge
import Def.CPythonListsort.Code.Correctness.MergeLoInvariant
/-!
# Semantic invariant for `merge_lo`

The reviewed safety invariant describes cursor geometry and storage validity.
This separate correctness invariant fixes immutable snapshots of the two
trimmed input runs and relates the emitted prefix, the live temporary suffix,
and the live main-data suffix to one shared stable-merge target.  Keeping this
layer separate prevents correctness-only order hypotheses from leaking into
the arbitrary-comparator safety theorem.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-! ## Public semantic input contract -/

/-- Direction-specific name for the shared post-trimming run contract. -/
abbrev MergeLoSemanticPre
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu) : Prop :=
  MergeSemanticPre lt call

end CPythonListsort
