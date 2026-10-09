import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ} :
-- imply
  max x y = if y < x then x else y := by
-- proof
  split_ifs with h
  · exact max_eq_left h.le
  · exact max_eq_right (not_lt.mp h)


-- created on 2019-06-18
