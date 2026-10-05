import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : 0 < a - b) :
-- imply
  b < a := by
-- proof
  exact sub_pos.mp h


-- created on 2023-04-15
