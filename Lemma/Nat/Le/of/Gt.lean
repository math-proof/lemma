import sympy.sets.sets
import sympy.Basic


@[path]
private lemma relax
  {x y : ℝ}
-- given
  (h : x > y) :
-- imply
  y ≤ x := by
-- proof
  exact h.le


-- created on 2020-05-11
