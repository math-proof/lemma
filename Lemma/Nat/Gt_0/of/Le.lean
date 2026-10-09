import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (hx : x > 0)
  (h : x ≤ y) :
-- imply
  y > 0 := by
-- proof
  exact lt_of_lt_of_le hx h


-- created on 2019-10-30
