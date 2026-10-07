import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
import Lemma.Random.Var.eq.Integral
import Lemma.Random.Cov.eq.Integral
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : Ω → ℝ}
-- given
  [PSpace π x] :
-- imply
  Covariance π x x = Variance π x := by
-- proof
  rw [Random.Var.eq.Integral, Random.Cov.eq.Integral]
  simp only [sq]


-- created on 2023-04-19
