import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Correctness.MergeLoInvariant
import sympy.atlas.CPythonListsort.Code.Correctness.MergeHiInvariant


namespace CPythonListsort

/--
[mergeLoTargetEntries_eq_mergeHiTargetEntries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeTargetConsistency.lean)
-/
@[path]
lemma mergeLoTargetEntries_eq_mergeHiTargetEntries
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {call : MergeAtCall (Occurrence alpha) nu} :
-- imply
  mergeLoTargetEntries lt call = mergeHiTargetEntries lt call := by
-- proof
  rfl

end CPythonListsort


-- created on 2026-10-23
