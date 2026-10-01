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
  Variance π x = Covariance π x x := by
-- proof
  rw [Variance.eq_integral, Covariance.eq_integral]
  simp only [sq]


-- created on 2023-04-14
