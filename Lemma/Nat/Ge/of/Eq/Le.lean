import sympy.Basic


@[main]
private lemma subst
  {y b x t k : ℝ}
-- given
  (h₀ : y = x * k + b)
  (h₁ : x ≤ t)
  (h₂ : k < 0) :
-- imply
  y ≥ t * k + b := by
-- proof
  rw [h₀]
  nlinarith


-- created on 2026-09-27
