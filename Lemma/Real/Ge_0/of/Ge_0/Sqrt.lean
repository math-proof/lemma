import Mathlib.Analysis.Real.Sqrt
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (_h : x ≥ 0) :
-- imply
  Real.sqrt x ≥ 0 :=
-- proof
  Real.sqrt_nonneg x


-- created on 2023-06-20
