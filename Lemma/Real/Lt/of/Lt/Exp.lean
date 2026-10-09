import sympy.functions.elementary.exponential
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x < y) :
-- imply
  Real.exp x < Real.exp y := by
-- proof
  exact Real.exp_lt_exp.mpr h


-- created on 2022-04-01
