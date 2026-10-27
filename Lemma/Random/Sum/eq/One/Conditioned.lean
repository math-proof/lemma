import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory


@[path]
private lemma main
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsFiniteMeasure π]
  {X : Ω → ι}
  {s : Set Ω}
-- given
  (h₀ : Measurable X)
  (h₁ : π s ≠ 0) :
-- imply
  ∑ i, (π[|s]).real (X ⁻¹' {i}) = 1 := by
-- proof
  have : IsProbabilityMeasure (π[|s]) := cond_isProbabilityMeasure h₁
  have hmap : ∑ i, ((π[|s]).map X) {i} = 1 := by
    rw [sum_measure_singleton (μ := (π[|s]).map X), Finset.coe_univ, measure_univ]
  have hpt : ∀ i, ((π[|s]).map X) {i} = π[|s] (X ⁻¹' {i}) :=
    fun i => Measure.map_apply h₀ (measurableSet_singleton i)
  rw [← ENNReal.toReal_one, ← hmap, ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
  simp [measureReal_def, hpt]


-- created on 2021-07-18
-- updated on 2026-10-26
