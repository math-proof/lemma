import sympy.Basic


@[main]
private lemma main
  {α ι : Type*}
  {A : Set α}
  {x : ι → Set α}
-- given
  (h : (⋃ i, x i) ∩ A = ∅) :
-- imply
  ∀ i, x i ∩ A = ∅ := by
-- proof
  rw [Set.iUnion_inter] at h
  exact Set.iUnion_eq_empty.mp h


-- created on 2020-08-10
