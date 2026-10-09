import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {x y a b : ℝ}
-- given
  (h₀ : |x| < a)
  (h₁ : |y| < b) :
-- imply
  |x * y| < a * b := by
-- proof
  rw [abs_mul]
  exact mul_lt_mul'' h₀ h₁ (abs_nonneg _) (abs_nonneg _)


-- created on 2023-04-15
