import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {𝕡 : Measure Ω}
  {a : Ω → α} {s : Ω → β}
  {f : α → ENNReal}
-- given
  (hP : PSpace 𝕡 (a, s))
  (hf : Measurable f)
  («s.bvar» : β) :
-- imply
  Expectation (ReferenceMeasure.measure.withDensity
      (fun «a.bvar» ↦ 𝕡.condProb (a, s) («a.bvar», «s.bvar»))) f =
    ∫⁻ «a.bvar», f «a.bvar» * 𝕡.condProb (a, s) («a.bvar», «s.bvar») ∂ReferenceMeasure.measure := by
-- proof
  simp only [Expectation]
  have hmp : Measurable (𝕡.prob (a, s)) := by
    simpa [Measure.prob] using Measure.measurable_rnDeriv (𝕡.map (a, s)) ReferenceMeasure.measure
  have hmc : Measurable (𝕡.condProb (a, s)) := by
    change Measurable (fun z : α × β ↦ 𝕡.prob (a, s) z /
      (𝕡.map (fun ω ↦ ((a, s) ω).2)).rnDeriv ReferenceMeasure.measure z.2)
    exact hmp.div ((Measure.measurable_rnDeriv (𝕡.map (fun ω ↦ ((a, s) ω).2))
      ReferenceMeasure.measure).comp measurable_snd)
  have hcd : Measurable (fun «a.bvar» : α ↦ 𝕡.condProb (a, s) («a.bvar», «s.bvar»)) :=
    hmc.comp (Measurable.prodMk measurable_id measurable_const)
  rw [lintegral_withDensity_eq_lintegral_mul _ hcd hf]
  simp only [Pi.mul_apply, mul_comm]


-- created on 2026-09-18
