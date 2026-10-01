import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : Ω → ℝ}
-- given
  [PSpace π x]
  (hx : Integrable x π)
  (hx2 : Integrable (fun ω => x ω ^ 2) π) :
-- imply
  Variance π x = ∫ ω, x ω ^ 2 ∂π - (∫ ω, x ω ∂π) ^ 2 := by
-- proof
  have : IsProbabilityMeasure π := PSpace.toIsProbabilityMeasure (x := x)
  have e : ∀ ω, (x ω - ∫ ω', x ω' ∂π) ^ 2 = x ω ^ 2 - (2 * (∫ ω', x ω' ∂π) * x ω - (∫ ω', x ω' ∂π) ^ 2) := fun ω => by ring
  have hc : ∫ _ : Ω, (∫ ω', x ω' ∂π) ^ 2 ∂π = (∫ ω', x ω' ∂π) ^ 2 := by simp
  have hA : Integrable (fun ω => 2 * (∫ ω', x ω' ∂π) * x ω) π := hx.const_mul _
  have hAC : Integrable (fun ω => 2 * (∫ ω', x ω' ∂π) * x ω - (∫ ω', x ω' ∂π) ^ 2) π := hA.sub (integrable_const _)
  rw [Variance.eq_integral]
  simp only [e]
  rw [integral_sub hx2 hAC, integral_sub hA (integrable_const _), integral_const_mul, hc]
  ring


-- created on 2026-09-27
