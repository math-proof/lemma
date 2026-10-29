import Mathlib.Probability.HasLaw
import Lemma.Random.Distributed.is.EqAe_Prob
open MeasureTheory ProbabilityTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {x : Ω → α}
  {ρ : α → ENNReal}
-- given
  [SinglePSpace π x]
  (hρ : Measurable ρ) :
-- imply
  HasLaw x (ReferenceMeasure.measure.withDensity ρ) π ↔
      π.prob x =ᵐ[ReferenceMeasure.measure] ρ := by
-- proof
  exact Random.Distributed.is.EqAe_Prob hρ


-- created on 2023-04-10
-- updated on 2026-10-29
