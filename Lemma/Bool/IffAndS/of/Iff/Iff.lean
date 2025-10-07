import sympy.Basic


@[main]
private lemma main
-- given
  (h₀ : p ↔ p')
  (h₁ : q ↔ q') :
-- imply
  p ∧ q ↔ p' ∧ q' := by
-- proof
  rw [h₀, h₁]


-- created on 2025-07-19
