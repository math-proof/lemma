import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
import Lemma.Random.Var.eq.Integral
open MeasureTheory


@[path]
private lemma offset
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : Ω → ℝ}
-- given
  [PSpace π x]
  [PSpace π (fun ω => x ω - ∫ ω', x ω' ∂π)]
  (hx : Integrable x π) :
-- imply
  Variance π (fun ω => x ω - ∫ ω', x ω' ∂π) = Variance π x := by
-- proof
  have : IsProbabilityMeasure π := PSpace.toIsProbabilityMeasure (x := x)
  have h0 : ∫ ω, (x ω - ∫ ω', x ω' ∂π) ∂π = 0 := by
    rw [integral_sub hx (integrable_const _)]
    simp
  simp only [Random.Var.eq.Integral, h0, sub_zero]


-- created on 2023-04-09
