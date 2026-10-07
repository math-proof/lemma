import sympy.stats.variance
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} {x : Ω → ℝ} [PSpace π x] :
-- imply
  Variance π x = ∫ ω, (x ω - ∫ ω', x ω' ∂π) ^ 2 ∂π := by
-- proof
  unfold Variance
  rw [Expectation.ofRV_self]
  exact Expectation.ofRV_eq_integral (Continuous.aestronglyMeasurable (by fun_prop))


-- created on 2026-10-07
