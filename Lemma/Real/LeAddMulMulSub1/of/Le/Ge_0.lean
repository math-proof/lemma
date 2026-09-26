import sympy.Basic


@[main]
private lemma main
  {p x y : ℝ}
-- given
  (h₀ : 0 ≤ p)
  (h₁ : x ≤ y) :
-- imply
  p * x + (1 - p) * y ≤ y := by
-- proof
  nlinarith [mul_le_mul_of_nonneg_left h₁ h₀]


-- created on 2026-09-26
