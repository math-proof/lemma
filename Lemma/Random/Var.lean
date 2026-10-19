import Mathlib.Probability.Independence.Integration
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
  𝕍𝕒𝕣 π (fun ω => x ω - ∫ ω', x ω' ∂π) = 𝕍𝕒𝕣 π x := by
-- proof
  have : IsProbabilityMeasure π := PSpace.toIsProbabilityMeasure (x := x)
  have h0 : ∫ ω, (x ω - ∫ ω', x ω' ∂π) ∂π = 0 := by
    rw [integral_sub hx (integrable_const _)]
    simp
  simp only [Random.Var.eq.Integral, h0, sub_zero]


-- created on 2023-04-09
