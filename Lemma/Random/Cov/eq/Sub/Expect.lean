import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x y : Ω → ℝ}
-- given
  [PSpace π x]
  [PSpace π y]
  (hx : Integrable x π)
  (hy : Integrable y π)
  (hxy : Integrable (fun ω => x ω * y ω) π) :
-- imply
  Covariance π x y = ∫ ω, x ω * y ω ∂π - (∫ ω, x ω ∂π) * ∫ ω, y ω ∂π := by
-- proof
  have : IsProbabilityMeasure π := PSpace.toIsProbabilityMeasure (x := x)
  have e : ∀ ω, (x ω - ∫ ω', x ω' ∂π) * (y ω - ∫ ω', y ω' ∂π) = x ω * y ω - ((∫ ω', x ω' ∂π) * y ω + (∫ ω', y ω' ∂π) * x ω - (∫ ω', x ω' ∂π) * ∫ ω', y ω' ∂π) := fun ω => by ring
  have hc : ∫ _ : Ω, (∫ ω', x ω' ∂π) * (∫ ω', y ω' ∂π) ∂π = (∫ ω', x ω' ∂π) * ∫ ω', y ω' ∂π := by simp
  have hA : Integrable (fun ω => (∫ ω', x ω' ∂π) * y ω) π := hy.const_mul _
  have hB : Integrable (fun ω => (∫ ω', y ω' ∂π) * x ω) π := hx.const_mul _
  have hAB : Integrable (fun ω => (∫ ω', x ω' ∂π) * y ω + (∫ ω', y ω' ∂π) * x ω) π := hA.add hB
  have hABC : Integrable (fun ω => (∫ ω', x ω' ∂π) * y ω + (∫ ω', y ω' ∂π) * x ω - (∫ ω', x ω' ∂π) * ∫ ω', y ω' ∂π) π := hAB.sub (integrable_const _)
  rw [Covariance.eq_integral]
  simp only [e]
  rw [integral_sub hxy hABC, integral_sub hAB (integrable_const _), integral_add hA hB, integral_const_mul, integral_const_mul, hc]
  ring


-- created on 2026-09-27
