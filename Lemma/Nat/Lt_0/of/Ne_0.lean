import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a : ℝ}
-- given
  (ha : a ≤ 0)
  (h : a ≠ 0) :
-- imply
  a < 0 := by
-- proof
  exact lt_of_le_of_ne ha h


-- created on 2020-02-14
