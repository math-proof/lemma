import Mathlib.MeasureTheory.Measure.WithDensity
import Syntax.Probability.Expectation.Elab
import Initialize.Tactic.Attr.Basic
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω}
  {a : Ω → α} {s : Ω → β}
  {f : α → ENNReal}
-- given
  (hP : SinglePSpace π (a, s))
  (hf : Measurable f)
  («\sf{s}» : β) :
-- imply
  Expectation.condRV π a s f «\sf{s}» =
    ∫⁻ «\sf{a}», f «\sf{a}» * ℙ[π](a = «\sf{a}» | s = «\sf{s}») ∂ReferenceMeasure.measure := by
-- proof
  simp only [Expectation.condRV, expectation_ennreal]
  have hmp : Measurable (π.prob (a, s)) := by
    simpa [Measure.prob] using Measure.measurable_rnDeriv (π.map (a, s)) ReferenceMeasure.measure
  have hmc : Measurable (π.condProb (a, s)) := by
    change Measurable (fun z : α × β ↦ π.prob (a, s) z /
      (π.map (fun ω ↦ ((a, s) ω).2)).rnDeriv ReferenceMeasure.measure z.2)
    exact hmp.div ((Measure.measurable_rnDeriv (π.map (fun ω ↦ ((a, s) ω).2))
      ReferenceMeasure.measure).comp measurable_snd)
  have hcd : Measurable (fun «\sf{a}» : α ↦ π.condProb (a, s) («\sf{a}», «\sf{s}»)) :=
    hmc.comp (Measurable.prodMk measurable_id measurable_const)
  rw [lintegral_withDensity_eq_lintegral_mul _ hcd hf]
  simp only [Pi.mul_apply, mul_comm]


-- created on 2026-09-18
-- updated on 2026-11-02
