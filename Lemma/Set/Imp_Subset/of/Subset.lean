import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : ∀ X : Set α, X ⊆ A → X ⊆ B) :
-- imply
  A ⊆ B := by
-- proof
  exact h A Set.Subset.rfl


-- created on 2022-09-20
