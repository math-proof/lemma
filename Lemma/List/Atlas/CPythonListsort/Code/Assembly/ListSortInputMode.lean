import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Assembly.ListSortInputMode
open CPythonListsort


namespace CPythonListsort

/--
[listSort_eq_listSortImpl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortInputMode.lean)
-/
@[path]
lemma listSort_eq_listSortImpl
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {reverse : Bool}
  {input : ListSortInput κ ν} :
-- imply
  listSort? lt reverse input = listSortImpl? lt reverse input.hasKeyfunc input.slice :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[initialMergeState_valuesMode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortInputMode.lean)
-/
@[path]
lemma initialMergeState_valuesMode
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {input : ListSortInput κ ν} :
-- imply
  SortSlice.ValuesModeInvariant (initialMergeState lt input.hasKeyfunc input.slice).1.a.hasValues (initialMergeState lt input.hasKeyfunc input.slice).1.data := by
-- proof
  simpa using input.valuesMode

end CPythonListsort


-- created on 2026-10-23
