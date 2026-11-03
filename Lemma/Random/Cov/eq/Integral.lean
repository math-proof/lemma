import Def.Probability.Moments.Variance
import Lemma.Random.Expect.eq.Integral
open MeasureTheory Random


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} {x y : Ω → ℝ} [PSpace π x] [PSpace π y] :
-- imply
  ℂ𝕠𝕧 π x y = ∫ ω, (x ω - ∫ ω', x ω' ∂π) * (y ω - ∫ ω', y ω' ∂π) ∂π := by
-- proof
  unfold ℂ𝕠𝕧
  have hId {z : Ω → ℝ} [PSpace π z] :
    Expectation.ofRV π z (fun a : ℝ ↦ a) = ∫ ω, z ω ∂π := by
    change 𝔼[z: π](z) = _
    apply Expect.eq.Integral
  rw [hId, hId]
  exact OfRV.eq.Integral.of.AEStronglyMeasurable_Map (Continuous.aestronglyMeasurable (by fun_prop))


-- created on 2026-10-07
-- updated on 2026-11-03
