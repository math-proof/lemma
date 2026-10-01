import Mathlib.Data.Real.Sign
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x > 0) :
-- imply
  Real.sign x = 1 := by
-- proof
  exact Real.sign_of_pos h


-- created on 2026-09-27
