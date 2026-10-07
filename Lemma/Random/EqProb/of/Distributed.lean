import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
import Lemma.Random.Distributed.is.EqAe_Prob
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {x : Ω → α}
  {ρ : α → ENNReal}
  {D : Distribution π ρ}
-- given
  [SinglePSpace π x]
  (h : x ~ D) :
-- imply
  π.prob x =ᵐ[ReferenceMeasure.measure] ρ := by
-- proof
  exact (Random.Distributed.is.EqAe_Prob D).mp h


-- created on 2023-04-30
