import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (hx : x < 0)
  (h : x ≥ y) :
-- imply
  y < 0 := by
-- proof
  exact lt_of_le_of_lt h hx


-- created on 2021-08-30
