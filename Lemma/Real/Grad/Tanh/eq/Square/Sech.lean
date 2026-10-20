import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import sympy.functions.elementary.hyperbolic
import sympy.Basic


@[path]
private lemma main
  (x : ℝ) :
-- imply
  deriv Real.tanh x = Real.sech x ^ 2 := by
-- proof
  rw [funext Real.tanh_eq_sinh_div_cosh]
  have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  simp only [← Pi.div_apply]
  rw [(Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hcosh |>.deriv, Real.sech]
  field_simp [hcosh]
  linarith [Real.cosh_sq_sub_sinh_sq x]


-- created on 2023-11-26
-- updated on 2026-10-17
