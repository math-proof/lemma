module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Structure.CPythonListsort.Code.Correctness.MergeLoInvariant
public import Theorem.CPythonListsort.Code.Correctness.MergeHiInvariant


public section

namespace CPythonListsort

/--
[mergeLoTargetEntries_eq_mergeHiTargetEntries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeTargetConsistency.lean)
-/
@[path]
theorem mergeLoTargetEntries_eq_mergeHiTargetEntries
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
