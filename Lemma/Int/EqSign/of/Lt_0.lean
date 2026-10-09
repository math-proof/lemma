import Mathlib.Data.Real.Sign
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x < 0) :
-- imply
  Real.sign x = -1 := by
-- proof
  exact Real.sign_of_neg h


-- created on 2023-05-29
