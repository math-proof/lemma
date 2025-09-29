import sympy.Basic


@[main]
private lemma main
  {A B C : Set α}
-- given
  (h₀ : A ⊆ B)
  (h₁ : B ⊆ C) :
-- imply
  A ⊆ C :=
-- proof
  subset_trans h₀ h₁


-- created on 2025-07-21
