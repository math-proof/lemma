import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (hx : x ≥ 0)
  (h : x < y) :
-- imply
  y ≠ 0 := by
-- proof
  exact ne_of_gt (lt_of_le_of_lt hx h)


-- created on 2021-09-18
