import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a b : ℝ}
-- given
  (h₀ : x ≥ 0)
  (h₁ : a > b) :
-- imply
  a * x ≥ b * x := by
-- proof
  exact mul_le_mul_of_nonneg_right h₁.le h₀


-- created on 2019-06-11
