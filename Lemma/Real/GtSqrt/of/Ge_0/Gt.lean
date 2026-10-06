import Mathlib.Analysis.Real.Sqrt
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (hx : x ≥ 0)
  (h : y > x) :
-- imply
  Real.sqrt y > Real.sqrt x :=
-- proof
  Real.sqrt_lt_sqrt_iff hx |>.mpr h


-- created on 2019-06-13
-- updated on 2023-05-02
