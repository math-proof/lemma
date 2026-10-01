import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
open MeasureTheory


@[main]
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
  exact (Distributed_iff D).mpr h


-- created on 2026-09-27
