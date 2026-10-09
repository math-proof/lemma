import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : a ≤ x)
  (h₁ : x < b) :
-- imply
  b > a := by
-- proof
  exact lt_of_le_of_lt h₀ h₁


-- created on 2019-11-23
