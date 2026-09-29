import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (hx : x > 0)
  (h : x ≤ a) :
-- imply
  1 / x ≥ 1 / a := by
-- proof
  exact one_div_le_one_div_of_le hx h


-- created on 2026-09-27
