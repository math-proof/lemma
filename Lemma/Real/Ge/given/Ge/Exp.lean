import Mathlib.Analysis.Complex.Exponential
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≥ y) :
-- imply
  Real.exp x ≥ Real.exp y :=
-- proof
  Real.exp_le_exp.mpr h


-- created on 2022-03-31
