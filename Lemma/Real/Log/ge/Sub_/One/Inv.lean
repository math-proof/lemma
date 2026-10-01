import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (hx : x > 0) :
-- imply
  Real.log x ≥ 1 - 1 / x := by
-- proof
  have := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at this
  rw [one_div]
  linarith


-- created on 2019-09-21
