import Mathlib.Probability.HasLaw
import Lemma.Random.Distributed.is.EqAe_Prob
open MeasureTheory ProbabilityTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  [μ : ReferenceMeasure α]
  {π : Measure Ω}
  {x : Ω → α}
  {ρ : α → ENNReal}
-- given
  [SinglePSpace π x]
  (hρ : Measurable ρ)
  (h : HasLaw x (μ.measure.withDensity ρ) π) :
-- imply
  π.prob x =ᵐ[μ.measure] ρ := by
-- proof
  exact (Random.Distributed.is.EqAe_Prob hρ).mp h


-- created on 2023-04-30
-- updated on 2026-11-14
