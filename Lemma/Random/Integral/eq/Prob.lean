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
  {s : Set α}
-- given
  [SinglePSpace π x]
  (hs : MeasurableSet s) :
-- imply
  ∫⁻ a in s, π.prob x a ∂ReferenceMeasure.measure = Probability π x s := by
-- proof
  unfold Probability
  rw [SinglePSpace.map_eq_withDensity_density, withDensity_apply _ hs]


-- created on 2023-04-18
