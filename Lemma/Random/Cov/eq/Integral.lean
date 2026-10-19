import sympy.stats.variance
import Lemma.Random.Expect.eq.Integral.Id
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} {x y : Ω → ℝ} [PSpace π x] [PSpace π y] :
-- imply
  ℂ𝕠𝕧 π x y = ∫ ω, (x ω - ∫ ω', x ω' ∂π) * (y ω - ∫ ω', y ω' ∂π) ∂π := by
-- proof
  unfold ℂ𝕠𝕧
  rw [Random.Expect.eq.Integral.Id, Random.Expect.eq.Integral.Id]
  exact Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map (Continuous.aestronglyMeasurable (by fun_prop))


-- created on 2026-10-07
