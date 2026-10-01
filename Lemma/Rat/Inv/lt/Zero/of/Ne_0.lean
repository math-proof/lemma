import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a : ℝ}
-- given
  (ha : a ≤ 0)
  (h : a ≠ 0) :
-- imply
  1 / a < 0 := by
-- proof
  exact one_div_neg.mpr (lt_of_le_of_ne ha h)


-- created on 2023-04-22
