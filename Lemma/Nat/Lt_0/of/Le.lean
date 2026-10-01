import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (hy : y < 0)
  (h : x ≤ y) :
-- imply
  x < 0 := by
-- proof
  exact lt_of_le_of_lt h hy


-- created on 2021-09-01
