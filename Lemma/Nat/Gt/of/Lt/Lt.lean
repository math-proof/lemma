import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : a < x)
  (h₁ : x < b) :
-- imply
  b > a := by
-- proof
  exact lt_trans h₀ h₁


-- created on 2020-01-06
