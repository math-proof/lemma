import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
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
  exact (Distributed_iff D).mp h


-- created on 2023-04-30
