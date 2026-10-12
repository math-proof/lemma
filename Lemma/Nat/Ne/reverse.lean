import Mathlib.Basic.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : a ≠ b) :
-- imply
  b ≠ a :=
-- proof
  Ne.symm h


-- created on 2020-02-07
