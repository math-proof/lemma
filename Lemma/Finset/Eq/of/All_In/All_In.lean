import sympy.Basic


@[main]
private lemma main
  {A B : Finset α}
-- given
  (h₀ : ∀ x ∈ A, x ∈ B)
  (h₁ : ∀ x ∈ B, x ∈ A) :
-- imply
  A = B := by
-- proof
  aesop


-- created on 2025-12-30
