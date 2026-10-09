import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y a b : ℝ}
-- given
  (h₀ : |x| ≤ a)
  (h₁ : |y| ≤ b) :
-- imply
  |x * y| ≤ a * b := by
-- proof
  rw [abs_mul]
  exact mul_le_mul h₀ h₁ (abs_nonneg _) ((abs_nonneg _).trans h₀)


-- created on 2023-04-15
