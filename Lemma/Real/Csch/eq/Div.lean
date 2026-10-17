import Mathlib.Analysis.Complex.Trigonometric
import sympy.functions.elementary.hyperbolic
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.csch x = 2 / (Real.exp x - Real.exp (-x)) := by
-- proof
  rw [Real.csch, Real.sinh_eq]
  field_simp


-- created on 2026-10-11
-- updated on 2026-10-17
