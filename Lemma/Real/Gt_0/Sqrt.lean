import Mathlib.Analysis.Real.Sqrt
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x > 0) :
-- imply
  Real.sqrt x > 0 :=
-- proof
  Real.sqrt_pos.mpr h


-- created on 2023-06-20
