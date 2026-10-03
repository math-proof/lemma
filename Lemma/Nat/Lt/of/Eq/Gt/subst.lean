import sympy.Basic


@[main]
private lemma main
  {y b x t k : ℝ}
-- given
  (h₀ : y = x * k + b)
  (h₁ : x > t)
  (h₂ : k < 0) :
-- imply
  y < t * k + b := by
-- proof
  nlinarith [mul_lt_mul_of_neg_left h₁ h₂]


-- created on 2020-07-16
