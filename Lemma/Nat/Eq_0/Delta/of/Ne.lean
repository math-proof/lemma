import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℤ}
-- given
  (h : x ≠ y) :
-- imply
  (if x = y then (1 : ℝ) else 0) = 0 :=
-- proof
  ite_eq_right h


-- created on 2019-05-03
