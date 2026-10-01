import sympy.Basic


@[main]
private lemma subst
  {y x k b t : ℝ}
-- given
  (h₀ : y = x * k + b)
  (h₁ : x > t)
  (h₂ : k < 0) :
-- imply
  y < t * k + b := by
-- proof
  have := mul_lt_mul_of_neg_right h₁ h₂
  rw [h₀]
  linarith


-- created on 2020-07-16
