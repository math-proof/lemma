import sympy.Basic


@[main]
private lemma main
  {α ι : Type*}
  {x : ι → Set α}
-- given
  (h : (⋃ i, x i) = ∅) :
-- imply
  ∀ i, x i = ∅ := by
-- proof
  exact Set.iUnion_eq_empty.mp h


-- created on 2020-08-09
-- updated on 2023-06-01
