import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[main]
private lemma main
-- given
  (x : ℝ) :
-- imply
  Real.sinh x = Real.tanh x * Real.cosh x := by
-- proof
  have hc : Real.cosh x ≠ 0 :=
    (Real.cosh_pos x).ne'
  rw [Real.tanh_eq_sinh_div_cosh, div_mul_cancel₀ _ hc]


-- created on 2023-11-26
