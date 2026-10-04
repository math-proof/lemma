import sympy.Basic


@[main]
private lemma main
  {x y z : ℝ}
-- given
  (h₀ : x * z < y * z)
  (h₁ : 0 < z) :
-- imply
  x < y := by
-- proof
  exact lt_of_mul_lt_mul_right h₀ h₁.le


-- created on 2019-08-20
