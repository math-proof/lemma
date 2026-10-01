import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x ≥ 0)
  (h₁ : x < y) :
-- imply
  max (y ^ 2) (x ^ 2) = y ^ 2 := by
-- proof
  exact max_eq_left (by nlinarith)


-- created on 2019-06-22
