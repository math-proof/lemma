import Mathlib
import sympy.Basic


namespace CPythonListsort

/--
[listsort_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSafety.lean)
-/
@[path]
lemma listsort_safe
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {reverse : Bool}
  {input : ListSortInput κ ν}
-- given
  (hSize : input.slice.entries.size ≤ PY_LIST_MAX) :
-- imply
  let execution := listSortTraced? lt reverse input (∃ result, execution.result = some result) ∧ execution.trace.fuelExhausted = false ∧ execution.trace.stackDepthMax ≤ 61 ∧ 61 < MAX_MERGE_PENDING ∧ execution.trace.allAccessesInBounds := by
-- proof
  obtain ⟨result, hSafe⟩ := listSortTraced_safe lt reverse input hSize
  exact ⟨⟨result, hSafe.resultEq⟩, hSafe.traceSafety.fuel,
    hSafe.traceSafety.stackDepth,
    by norm_num [MAX_MERGE_PENDING],
    listSortTraced_allAccessesInBounds lt reverse input hSize⟩

end CPythonListsort

namespace CPythonListsort

/--
[listsort_safe_keyed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSafety.lean)
-/
@[path]
lemma listsort_safe_keyed
  {κ : Type u}
  {ν : Type v}
  {lt : κ → κ → Bool}
  {reverse : Bool}
  {entries : Array (κ × ν)}
-- given
  (hSize : entries.size ≤ PY_LIST_MAX) :
-- imply
  let execution := listSortTraced? lt reverse (ListSortInput.keyed entries) (∃ result, execution.result = some result) ∧ execution.trace.fuelExhausted = false ∧ execution.trace.stackDepthMax ≤ 61 ∧ 61 < MAX_MERGE_PENDING ∧ execution.trace.allAccessesInBounds := by
-- proof
  apply listsort_safe lt reverse (ListSortInput.keyed entries)
  simpa [ListSortInput.keyed] using hSize

end CPythonListsort

namespace CPythonListsort

/--
[listsort_safe_unkeyed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSafety.lean)
-/
@[path]
lemma listsort_safe_unkeyed
  {κ : Type u}
  {ν : Type v}
  {lt : α → α → Bool}
  {reverse : Bool}
  {xs : Array α}
-- given
  (hSize : xs.size ≤ PY_LIST_MAX) :
-- imply
  let execution := listSortTraced? lt reverse (ListSortInput.unkeyed xs) (∃ result, execution.result = some result) ∧ execution.trace.fuelExhausted = false ∧ execution.trace.stackDepthMax ≤ 61 ∧ 61 < MAX_MERGE_PENDING ∧ execution.trace.allAccessesInBounds := by
-- proof
  simpa using
    listsort_safe (κ := α) (ν := PUnit) lt reverse (ListSortInput.unkeyed xs)
      (by simpa [ListSortInput.unkeyed, ListSortInput.unkeyedAs] using hSize)

end CPythonListsort


-- created on 2026-10-23
