import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
import Lemma.Random.Map.eq.WithDensityProb
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
  Probability π x s = ∫⁻ a in s, π.prob x a ∂ReferenceMeasure.measure := by
-- proof
  unfold Probability
  rw [Random.Map.eq.WithDensityProb, withDensity_apply _ hs]


-- created on 2023-03-20
