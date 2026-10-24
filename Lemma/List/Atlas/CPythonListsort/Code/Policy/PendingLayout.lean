import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Policy.PendingLayout
open CPythonListsort


namespace CPythonListsort

/--
[PendingRunsCover.totalLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/PendingLayout.lean)
-/
@[path]
lemma PendingRunsCover.totalLength
  {cursor limit : Nat}
  {runs : List PendingRun}
-- given
  (h : PendingRunsCover cursor limit runs) :
-- imply
  cursor + (runs.map fun run => run.len.toNat).sum = limit := by
-- proof
  induction runs generalizing cursor with
  | nil =>
    simpa [PendingRunsCover] using h
  | cons run rest ih =>
    obtain ⟨hbase, _, _, _, hrest⟩ := h
    simpa [PendingRunsCover, PendingRun.endIndex, hbase, Nat.add_assoc] using
      ih hrest

end CPythonListsort

namespace CPythonListsort

/--
[exists_pair_split_of_getElem?_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/PendingLayout.lean)
-/
@[path]
prefix/pair/suffix decomposition of `toList`. -/
lemma Array.exists_pair_split_of_getElem?_eq_some
  {α : Type u} {xs : Array α} {i : Nat} {left right : α}
  (hleft : xs[i]? = some left)
  (hright : xs[i + 1]? = some right) :
  ∃ before after,
    before.length = i ∧
    xs.toList = before ++ left :: right :: after := by
  obtain ⟨hi, hleft'⟩ := getElem?_eq_some_iff.mp hleft
  obtain ⟨hi1, hright'⟩ := getElem?_eq_some_iff.mp hright
  let before := xs.toList.take i
  let after := xs.toList.drop (i + 2)
  refine ⟨before, after, ?_, ?_⟩
  · simp [before, Nat.le_of_lt hi]
  · have hleftList : xs.toList[i] = left := by
    simpa using hleft'
    have hrightList : xs.toList[i + 1] = right := by
      simpa using hright'
    rw [← List.take_append_drop i xs.toList]
    rw [List.drop_eq_getElem_cons (by simpa using hi)]
    rw [hleftList]
    rw [List.drop_eq_getElem_cons (by simpa using hi1)]
    rw [hrightList]

end CPythonListsort

/--
[Array.exists_pair_split_of_getElem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/PendingLayout.lean)
-/
@[path]
private lemma exists_pair_split_of_getElem_eq
  {α : Type u}
  {xs : Array α}
  {i : Nat}
  {left right : α}
-- given
  (hleft : xs[i]? = some left)
  (hright : xs[i + 1]? = some right) :
-- imply
  ∃ before after, before.length = i ∧ xs.toList = before ++ left :: right :: after := by
-- proof
  apply CPythonListsort.Array.exists_pair_split_of_getElem hleft hright


-- created on 2026-10-23
