import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : Ω → ℝ}
-- given
  [PSpace π x] :
-- imply
  Variance π x = ∫ ω, (x ω - ∫ ω', x ω' ∂π) ^ 2 ∂π := by
-- proof
  exact Variance.eq_integral


-- created on 2026-09-27
