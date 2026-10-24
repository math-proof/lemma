import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Assembly.ListSortTermination


namespace CPythonListsort

/--
[listSortImplTraced_allAccessesInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortLocalBounds.lean)
-/
@[path]
lemma listSortImplTraced_allAccessesInBounds
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {input : SortSlice κ ν}
-- given
  (reverse hasKeyfunc : Bool)
  (hSize : input.entries.size ≤ PY_LIST_MAX)
  (hMode : SortSlice.ValuesModeInvariant hasKeyfunc input) :
-- imply
  (listSortImplTraced? lt reverse hasKeyfunc input).trace.allAccessesInBounds := by
-- proof
  rcases listSortImplTraced_safe lt reverse hasKeyfunc input hSize hMode with
    ⟨result, hSafe⟩
  exact hSafe.traceSafety.accessesInBounds

end CPythonListsort

namespace CPythonListsort

/--
[listSortTraced_allAccessesInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortLocalBounds.lean)
-/
@[path]
lemma listSortTraced_allAccessesInBounds
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {reverse : Bool}
  {input : ListSortInput κ ν}
-- given
  (hSize : input.slice.entries.size ≤ PY_LIST_MAX) :
-- imply
  (listSortTraced? lt reverse input).trace.allAccessesInBounds := by
-- proof
  obtain ⟨result, hSafe⟩ := listSortTraced_safe lt reverse input hSize
  exact hSafe.traceSafety.accessesInBounds

end CPythonListsort


-- created on 2026-10-23
