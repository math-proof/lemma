import Def.Probability.Moments.Variance
import Lemma.Random.Expect.eq.Integral.Id
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} {x : Ω → ℝ} [PSpace π x] :
-- imply
  𝕍𝕒𝕣 π x = ∫ ω, (x ω - ∫ ω', x ω' ∂π) ^ 2 ∂π := by
-- proof
  unfold 𝕍𝕒𝕣
  rw [Random.Expect.eq.Integral.Id]
  exact Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map (Continuous.aestronglyMeasurable (by fun_prop))


-- created on 2026-10-07
