import Lemma.Real.Tanh.eq.Div.Add.Exp
import sympy.functions.elementary.hyperbolic
import sympy.Basic
open Real


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.coth x = (Real.exp x + Real.exp (-x)) / (Real.exp x - Real.exp (-x)) := by
-- proof
  rw [Real.coth, Tanh.eq.Div.Add.Exp, one_div, inv_div]


-- created on 2023-11-26
-- updated on 2026-10-17
