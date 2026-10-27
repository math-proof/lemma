import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Initialize.Tactic.Attr.Basic
open MeasureTheory InformationTheory


@[path]
private lemma main
  [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ ν : Measure α}
-- given
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (h₀ : μ ≪ ν)
  (h₁ : Integrable (llr μ ν) μ) :
-- imply
  klDiv μ ν = ENNReal.ofReal (∑ x, μ.real {x} * llr μ ν x) := by
-- proof
  rw [klDiv_of_ac_of_integrable h₀ h₁, integral_fintype h₁, measureReal_def, measureReal_def,
    measure_univ, measure_univ]
  simp [smul_eq_mul]


-- created on 2023-03-25
-- updated on 2026-10-26
