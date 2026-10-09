import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x y : ℝ}
-- given
  (h₀ : a > b)
  (h₁ : x ≤ y) :
-- imply
  (a - b) * x ≤ (a - b) * y := by
-- proof
  exact mul_le_mul_of_nonneg_left h₁ (by linarith)


-- created on 2019-08-01
