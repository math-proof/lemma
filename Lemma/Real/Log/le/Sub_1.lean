import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (hx : x > 0) :
-- imply
  Real.log x ≤ x - 1 := by
-- proof
  exact Real.log_le_sub_one_of_pos hx


-- created on 2026-09-27
