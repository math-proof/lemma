import sympy.Basic


@[path]
private lemma main
  {A X B : Set α}
-- given
  (h₀ : A ⊆ X)
  (h₁ : B ⊇ X) :
-- imply
  A ⊆ B :=
-- proof
  subset_trans h₀ h₁


-- created on 2021-06-29
