import Mathlib.Basic.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : a = b) :
-- imply
  a ≤ b :=
-- proof
  le_of_eq h


-- created on 2021-12-27
