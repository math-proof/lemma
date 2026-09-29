import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (ha : a > 0)
  (h : x > a) :
-- imply
  1 / x < 1 / a := by
-- proof
  exact one_div_lt_one_div_of_lt ha h


-- created on 2026-09-27
