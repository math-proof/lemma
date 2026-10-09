import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
import Lemma.Random.Distributed.is.EqAe_Prob
open MeasureTheory


@[path]
private lemma given
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {x : Ω → α}
  {ρ : α → ENNReal}
  {D : Distribution π ρ}
-- given
  [SinglePSpace π x]
  (h : π.prob x =ᵐ[ReferenceMeasure.measure] ρ) :
-- imply
  x ~ D := by
-- proof
  exact (Random.Distributed.is.EqAe_Prob D).mpr h


-- created on 2023-04-30
