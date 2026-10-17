import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import sympy.Basic


@[path]
private lemma main
-- given
  (x : ℝ) :
-- imply
  Real.log (Real.sigmoid x) + Real.log (Real.sigmoid (-x)) =
    Real.log (Real.sigmoid x * (1 - Real.sigmoid x)) := by
-- proof
  have hpos : 0 < Real.sigmoid x := Real.sigmoid_pos x
  have hlt : Real.sigmoid x < 1 := Real.sigmoid_lt_one x
  rw [Real.sigmoid_neg, ← Real.log_mul hpos.ne' (sub_pos.mpr hlt).ne']


-- created on 2026-10-11
-- updated on 2026-10-17
