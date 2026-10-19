import Mathlib.Probability.Independence.Integration
import Lemma.Random.Cov.eq.Integral
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x y : Ω → ℝ}
-- given
  [PSpace π x]
  [PSpace π y] :
-- imply
  ℂ𝕠𝕧 π x y = ∫ ω, (x ω - ∫ ω', x ω' ∂π) * (y ω - ∫ ω', y ω' ∂π) ∂π := by
-- proof
  exact Random.Cov.eq.Integral


-- created on 2023-03-24
