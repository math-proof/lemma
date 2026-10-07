import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
import Lemma.Random.Cov.eq.Integral
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x y : Ω → ℝ}
-- given
  [PSpace π x]
  [PSpace π y]
  (h : ProbabilityTheory.IndepFun x y π)
  (hx : Integrable x π)
  (hy : Integrable y π) :
-- imply
  Covariance π x y = 0 := by
-- proof
  have : IsProbabilityMeasure π := PSpace.toIsProbabilityMeasure (x := x)
  have hi := h.comp (measurable_id.sub_const (∫ ω', x ω' ∂π)) (measurable_id.sub_const (∫ ω', y ω' ∂π))
  have h0 : ∫ ω, (x ω - ∫ ω', x ω' ∂π) ∂π = 0 := by
    rw [integral_sub hx (integrable_const _)]
    simp
  have hm : ∫ ω, (x ω - ∫ ω', x ω' ∂π) * (y ω - ∫ ω', y ω' ∂π) ∂π = (∫ ω, (x ω - ∫ ω', x ω' ∂π) ∂π) * ∫ ω, (y ω - ∫ ω', y ω' ∂π) ∂π :=
    hi.integral_mul_eq_mul_integral (hx.aestronglyMeasurable.sub aestronglyMeasurable_const)
      (hy.aestronglyMeasurable.sub aestronglyMeasurable_const)
  rw [Random.Cov.eq.Integral, hm, h0, zero_mul]


-- created on 2023-04-19
