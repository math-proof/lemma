import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Syntax.Probability.Expectation.Elab
import Instance.Analysis.Real.Numbers
open MeasureTheory
open scoped ENNReal.ToRealCoe


@[path]
private lemma main
  [MeasurableSpace Ω]
  [μ : ReferenceMeasure α] [ReferenceMeasure β]
  [NormedAddCommGroup ℰ] [NormedSpace ℝ ℰ] [CompleteSpace ℰ] [MeasurableSpace ℰ] [BorelSpace ℰ]
  {π : Measure Ω}
  {a : Ω → α} {s : Ω → β}
  {f : α → ℰ}
-- given
  (hP : SinglePSpace π (a, s))
  (hf : Measurable f)
  («\sf{s}» : β)
  (hlt : ∀ᵐ «\sf{a}» ∂μ.measure, ℙ[π](a = «\sf{a}» | s = «\sf{s}») < ⊤) :
-- imply
  Expectation.condRV π a s f «\sf{s}» =
    ∫ «\sf{a}», (ℙ[π](a = «\sf{a}» | s = «\sf{s}») : ℝ) • f «\sf{a}» ∂μ.measure := by
-- proof
  have := hf
  simp only [Expectation.condRV, expectation_bochner]
  have hmp : Measurable (π.prob (a, s)) := by
    simpa [Measure.prob] using Measure.measurable_rnDeriv (π.map (a, s)) ReferenceMeasure.measure
  have hmc : Measurable (π.condProb (a, s)) := by
    change Measurable (fun z : α × β ↦ π.prob (a, s) z /
      (π.map (fun ω ↦ ((a, s) ω).2)).rnDeriv ReferenceMeasure.measure z.2)
    exact hmp.div ((Measure.measurable_rnDeriv (π.map (fun ω ↦ ((a, s) ω).2))
      ReferenceMeasure.measure).comp measurable_snd)
  have hcd : Measurable (fun «\sf{a}» : α ↦ π.condProb (a, s) («\sf{a}», «\sf{s}»)) :=
    hmc.comp (Measurable.prodMk measurable_id measurable_const)
  rw [integral_withDensity_eq_integral_toReal_smul hcd hlt]


-- created on 2026-09-18
-- updated on 2026-11-14
