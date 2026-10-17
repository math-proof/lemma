import sympy.Basic


@[path]
private lemma main
  {A B X : Set α}
-- given
  (h₀ : A ⊆ X)
  (h₁ : B ⊇ X) :
-- imply
  B ⊇ A :=
-- proof
  subset_trans h₀ h₁


-- created on 2021-06-28
-- updated on 2026-10-17
