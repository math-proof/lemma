import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import sympy.Basic
open MeasureTheory ProbabilityTheory


@[path]
private lemma main
  [mΩ : MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {m : MeasurableSpace Ω}
  {x y : Ω → ℝ}
-- given
  (h₀ : m ≤ mΩ)
  (h₁ : MemLp x 2 π)
  (h₂ : MemLp y 2 π) :
-- imply
  covariance (condExp m π x) (condExp m π y) π =
    ∫ ω, condExp m π x ω * condExp m π y ω ∂π - (∫ ω, x ω ∂π) * ∫ ω, y ω ∂π := by
-- proof
  rw [covariance_eq_sub (MemLp.condExp one_le_two h₁) (MemLp.condExp one_le_two h₂),
    integral_condExp (μ := π) h₀, integral_condExp (μ := π) h₀]
  simp [Pi.mul_apply]


-- created on 2023-04-20
-- updated on 2026-10-17
