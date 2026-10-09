import sympy.Basic


@[path]
private lemma main
  {y b x t k : ℝ}
-- given
  (h₀ : y ≤ x * k + b)
  (h₁ : x < t)
  (h₂ : k ≥ 0) :
-- imply
  y ≤ t * k + b := by
-- proof
  nlinarith


-- created on 2026-10-03
