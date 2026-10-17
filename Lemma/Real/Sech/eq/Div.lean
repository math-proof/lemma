import Mathlib.Analysis.Complex.Trigonometric
import sympy.functions.elementary.hyperbolic
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.sech x = 2 / (Real.exp x + Real.exp (-x)) := by
-- proof
  rw [Real.sech, Real.cosh_eq]
  field_simp [(Real.cosh_pos x).ne']


-- created on 2026-10-11
-- updated on 2026-10-17
