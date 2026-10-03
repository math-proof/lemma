import sympy.Basic


@[main]
private lemma main
  {y b x t k : ℝ}
-- given
  (h₀ : x * k + b > y)
  (h₁ : x ≤ t)
  (h₂ : k > 0) :
-- imply
  t * k + b > y := by
-- proof
  have h₃ : x * k ≤ t * k := mul_le_mul_of_nonneg_right h₁ (le_of_lt h₂)
  linarith


-- created on 2019-07-30
