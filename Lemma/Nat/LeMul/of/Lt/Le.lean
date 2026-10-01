import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x y : ℝ}
-- given
  (h₀ : a < b)
  (h₁ : x ≤ y) :
-- imply
  (b - a) * x ≤ (b - a) * y := by
-- proof
  exact mul_le_mul_of_nonneg_left h₁ (by linarith)


-- created on 2020-01-05
