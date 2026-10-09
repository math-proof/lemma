import sympy.sets.sets
import sympy.Basic


@[path]
private lemma cancel
  {a b c d : ℝ}
-- given
  (h₀ : c ≠ 0)
  (h₁ : d ≠ 0) :
-- imply
  (a + 1 / c) / (b + 1 / d) = (a * c * d + d) / (b * c * d + c) := by
-- proof
  rw [show a * c * d + d = (a + 1 / c) * (c * d) by field_simp, show b * c * d + c = (b + 1 / d) * (c * d) by field_simp, mul_div_mul_right _ _ (mul_ne_zero h₀ h₁)]


-- created on 2020-06-29
