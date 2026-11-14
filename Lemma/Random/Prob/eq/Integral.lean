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
  Probability π x s = ∫⁻ a in s, π.prob x a ∂μ.measure := by
-- proof
  unfold Probability
  rw [Random.Map.eq.WithDensityProb, withDensity_apply _ hs]


-- created on 2023-03-20
-- updated on 2026-11-14
