import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
import Lemma.Random.Distributed.is.EqAe_Prob
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {x : Ω → α}
  {ρ : α → ENNReal}
-- given
  [SinglePSpace π x]
  (D : Distribution π ρ) :
-- imply
  x ~ D ↔ π.prob x =ᵐ[ReferenceMeasure.measure] ρ := by
-- proof
  exact Random.Distributed.is.EqAe_Prob D


-- created on 2023-04-10
