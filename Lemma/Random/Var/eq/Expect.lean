import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
import Lemma.Random.Var.eq.Integral
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : Ω → ℝ}
-- given
  [PSpace π x] :
-- imply
  Variance π x = ∫ ω, (x ω - ∫ ω', x ω' ∂π) ^ 2 ∂π := by
-- proof
  exact Random.Var.eq.Integral


-- created on 2023-03-24
