import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
`c⁻¹ * (γ * (c * Y) + c * Z) = Z + γ * Y` for `c ≠ 0`.
-/
@[main]
private lemma main
  {c γ Y Z : ℝ}
-- given
  (hc : c ≠ 0) :
-- imply
  c⁻¹ * (γ * (c * Y) + c * Z) = Z + γ * Y := by
-- proof
  rw [mul_add, mul_left_comm γ, inv_mul_cancel_left₀ hc, inv_mul_cancel_left₀ hc, add_comm]


-- created on 2026-10-07
