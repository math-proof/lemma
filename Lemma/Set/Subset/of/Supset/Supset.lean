import sympy.Basic


@[path]
private lemma main
  {A B X : Set α}
-- given
  (h₀ : X ⊇ A)
  (h₁ : B ⊇ X) :
-- imply
  B ⊇ A :=
-- proof
  subset_trans h₀ h₁


-- created on 2021-07-07
-- updated on 2026-10-17
