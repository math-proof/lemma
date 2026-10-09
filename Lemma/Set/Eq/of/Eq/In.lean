import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {A B : Set α}
  {a : α}
-- given
  (h : A \ {a} = B \ {a})
  (ha : a ∈ A) :
-- imply
  A = B ∪ {a} := by
-- proof
  have hA : A ∪ {a} = A := Set.union_eq_self_of_subset_right (Set.singleton_subset_iff.mpr ha)
  calc
    _ = A ∪ {a} := hA.symm
    _ = (A \ {a}) ∪ {a} := (Set.sdiff_union_self).symm
    _ = (B \ {a}) ∪ {a} := by rw [h]
    _ = B ∪ {a} := Set.sdiff_union_self


-- created on 2021-03-27
