import sympy.Basic


@[path]
private lemma main
  {A : Set α}
  {f : ι → Set α}
-- given
  (h₀ : (⋃ i, f i) ⊆ A) :
-- imply
  ∀ i, f i ⊆ A :=
-- proof
  Set.iUnion_subset_iff.mp h₀


-- created on 2020-09-13
-- updated on 2026-10-17
