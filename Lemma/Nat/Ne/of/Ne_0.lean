import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : a - b ≠ 0) :
-- imply
  a ≠ b := by
-- proof
  exact sub_ne_zero.mp h


-- created on 2021-09-19
