import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a : ℝ}
-- given
  (h₀ : x < 0)
  (h₁ : a > 0) :
-- imply
  x * a < 0 := by
-- proof
  exact mul_neg_of_neg_of_pos h₀ h₁


-- created on 2020-01-21
