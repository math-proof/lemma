import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h₀ : a ≠ 0)
  (h₁ : b ≠ 0) :
-- imply
  Real.log a - Real.log b = Real.log (a * b⁻¹) := by
-- proof
  rw [Real.log_mul h₀ (inv_ne_zero h₁), Real.log_inv, sub_eq_add_neg]


-- created on 2026-09-27
