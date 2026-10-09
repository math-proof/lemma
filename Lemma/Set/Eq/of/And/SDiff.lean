import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  (A B C : Set α)
-- given
  (h : A = B ∪ C) :
-- imply
  (A \ C = B \ C) ∧ C ⊆ A := by
-- proof
  constructor
  · rw [h]
    ext x
    simp only [Set.mem_sdiff, Set.mem_union]
    tauto
  · rw [h]
    exact Set.subset_union_right (s := B) (t := C)


-- created on 2021-03-31
