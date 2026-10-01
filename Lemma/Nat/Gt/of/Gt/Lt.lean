import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : b > x)
  (h₁ : a < x) :
-- imply
  b > a := by
-- proof
  exact lt_trans h₁ h₀


-- created on 2019-07-05
