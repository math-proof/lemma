import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a x b : ℝ}
-- given
  (h₀ : a ≤ x)
  (h₁ : b > x) :
-- imply
  a < b := by
-- proof
  exact lt_of_le_of_lt h₀ h₁


-- created on 2019-08-30
