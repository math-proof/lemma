import Mathlib.Probability.HasLaw
import Lemma.Random.Distributed.is.EqAe_Prob
open MeasureTheory ProbabilityTheory


@[path]
private lemma given
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {x : Ω → α}
  {ρ : α → ENNReal}
-- given
  [SinglePSpace π x]
  (hρ : Measurable ρ)
  (h : π.prob x =ᵐ[ReferenceMeasure.measure] ρ) :
-- imply
  HasLaw x (ReferenceMeasure.measure.withDensity ρ) π := by
-- proof
  exact (Random.Distributed.is.EqAe_Prob hρ).mpr h


-- created on 2023-04-30
-- updated on 2026-10-29
