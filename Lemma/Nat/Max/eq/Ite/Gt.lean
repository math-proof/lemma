import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {x y : α} :
-- imply
  max x y = if x > y then x else y := by
-- proof
  split_ifs with h
  · exact max_eq_left h.le
  · exact max_eq_right (not_lt.mp h)


-- created on 2026-09-27
