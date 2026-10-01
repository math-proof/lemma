import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {x y : α} :
-- imply
  min x y = if y ≥ x then x else y := by
-- proof
  split_ifs with h
  · exact min_eq_left h
  · exact min_eq_right (not_le.mp h).le


-- created on 2026-09-27
