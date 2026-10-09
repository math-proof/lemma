import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [LinearOrder α]
  {x y : α} :
-- imply
  max x y = if y ≤ x then x else y := by
-- proof
  split_ifs with h
  · exact max_eq_left h
  · exact max_eq_right (not_le.mp h).le


-- created on 2020-01-25
