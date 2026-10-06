import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.Basic


@[main]
private lemma main
  {x b : ℝ}
-- given
  (hb : 0 < b)
  (h : x ≥ b) :
-- imply
  Real.log x ≥ Real.log b :=
-- proof
  (Real.log_le_log_iff hb (lt_of_lt_of_le hb h)).mpr h


-- created on 2019-08-08
