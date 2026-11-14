import Mathlib.Probability.Independence.Integration
import Def.Probability.Moments.Variance
import Lemma.Random.Map.eq.WithDensityProb
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  [μ : ReferenceMeasure α]
  {π : Measure Ω}
  {x : Ω → α}
  {s : Set α}
-- given
  [SinglePSpace π x]
  (hs : MeasurableSet s) :
-- imply
  ∫⁻ a in s, π.prob x a ∂μ.measure = Probability π x s := by
-- proof
  unfold Probability
  rw [Random.Map.eq.WithDensityProb, withDensity_apply _ hs]


-- created on 2023-04-18
-- updated on 2026-11-14
