import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Exp


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : Real.exp x ≤ Real.exp y) :
-- imply
  x ≤ y :=
-- proof
  Real.exp_le_exp.mp h


-- created on 2022-03-31
