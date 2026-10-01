import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x > 0)
  (h₁ : y > 0) :
-- imply
  x + y > 0 := by
-- proof
  linarith


-- created on 2018-08-11
