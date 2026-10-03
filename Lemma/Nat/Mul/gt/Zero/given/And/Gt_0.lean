import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h₀ : a > 0)
  (h₁ : b > 0) :
-- imply
  a * b > 0 := by
-- proof
  exact mul_pos h₀ h₁


-- created on 2019-06-29
