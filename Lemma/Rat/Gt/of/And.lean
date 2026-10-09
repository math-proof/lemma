import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given.scale.positive
  {x y z : ℝ}
-- given
  (h₀ : x * z > y * z)
  (h₁ : z > 0) :
-- imply
  x > y := by
-- proof
  exact lt_of_mul_lt_mul_right h₀ h₁.le


-- created on 2026-09-27
