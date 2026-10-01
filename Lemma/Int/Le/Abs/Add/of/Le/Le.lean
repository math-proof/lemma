import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y a b : ℝ}
-- given
  (h₀ : |x| ≤ a)
  (h₁ : |y| ≤ b) :
-- imply
  |x + y| ≤ a + b := by
-- proof
  exact (abs_add_le x y).trans (add_le_add h₀ h₁)


-- created on 2023-04-15
