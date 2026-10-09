import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a x b y : ℝ}
-- given
  (h₀ : a ≤ x)
  (h₁ : b < y) :
-- imply
  a + b < x + y := by
-- proof
  exact add_lt_add_of_le_of_lt h₀ h₁


-- created on 2019-07-26
