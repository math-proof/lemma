import Mathlib.InformationTheory.KullbackLeibler.Basic
import Lemma.Random.KL.eq.Expect
open MeasureTheory InformationTheory Random


@[path]
private lemma main
  [MeasurableSpace α]
  {μ ν : Measure α}
-- given
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (h₀ : μ ≪ ν)
  (h₁ : Integrable (llr μ ν) μ) :
-- imply
  klDiv μ ν = ENNReal.ofReal (∫ x, llr μ ν x ∂μ) := by
-- proof
  rw [klDiv_of_ac_of_integrable h₀ h₁, measureReal_def, measureReal_def, measure_univ, measure_univ]
  simp


-- created on 2023-03-25
-- updated on 2026-10-17
