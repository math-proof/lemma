import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : a < x)
  (h₁ : x ≤ b) :
-- imply
  b > a := by
-- proof
  exact lt_of_lt_of_le h₀ h₁


-- created on 2020-01-04
