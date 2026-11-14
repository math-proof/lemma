import Def.Probability.Moments.Variance
import Lemma.Random.Expect.eq.Integral
open MeasureTheory Random


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} {x : Ω → ℝ} [PSpace π x] :
-- imply
  𝕍𝕒𝕣 π x = ∫ ω, (x ω - ∫ ω', x ω' ∂π) ^ 2 ∂π := by
-- proof
  change 𝕍𝕒𝕣 π x = _
  unfold 𝕍𝕒𝕣
  rw [show Expectation.ofRV π x (fun a : ℝ ↦ a) = ∫ ω, x ω ∂π by
    change 𝔼[x: π](x) = _
    apply Expect.eq.Integral]
  exact OfRV.eq.Integral.of.AEStronglyMeasurable_Map (Continuous.aestronglyMeasurable (by fun_prop))


-- created on 2026-10-07
-- updated on 2026-11-13
