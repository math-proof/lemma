import sympy.Basic


@[path]
private lemma main
  {A B X : Set α}
-- given
  (h₀ : X ⊇ A)
  (h₁ : X ⊆ B) :
-- imply
  A ⊆ B :=
-- proof
  subset_trans h₀ h₁


-- created on 2021-04-25
-- updated on 2026-10-17
