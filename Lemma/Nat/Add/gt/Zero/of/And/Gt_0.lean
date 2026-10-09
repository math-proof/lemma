import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {a b : ℝ}
-- given
  (h₀ : a > 0)
  (h₁ : b > 0) :
-- imply
  a + b > 0 := by
-- proof
  exact add_pos h₀ h₁


-- created on 2018-08-12
