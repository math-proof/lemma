import sympy.stats.variance
import sympy.Basic
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} {x y : Ω → ℝ} [PSpace π x] [PSpace π y] :
-- imply
  Covariance π x y = ∫ ω, (x ω - ∫ ω', x ω' ∂π) * (y ω - ∫ ω', y ω' ∂π) ∂π := by
-- proof
  unfold Covariance
  rw [Expectation.ofRV_self, Expectation.ofRV_self]
  exact Expectation.ofRV_eq_integral (Continuous.aestronglyMeasurable (by fun_prop))


-- created on 2026-10-07
