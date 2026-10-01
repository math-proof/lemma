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
-- given
  [SinglePSpace π x]
  (D : Distribution π ρ) :
-- imply
  x ~ D ↔ π.prob x =ᵐ[ReferenceMeasure.measure] ρ := by
-- proof
  exact Distributed_iff D


-- created on 2026-09-27
