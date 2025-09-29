import sympy.Basic


@[main]
private lemma main
  {X : ι → Set α}
  {A : Set α}
-- given
  (h : ∀ i : ι, X i ⊆ A) :
-- imply
  ⋃ i : ι, X i ⊆ A := by
-- proof
  rwa [Set.iUnion_subset_iff]


-- created on 2025-07-20
