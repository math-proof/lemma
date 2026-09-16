import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  [Countable α]
  [MeasurableSingletonClass α]
  {𝕡 : Measure Ω}
  {a : Ω → α} {s : Ω → β}
  {f : α → ENNReal}
-- given
  (hP : PSpace 𝕡 (a, s))
  (hf : Measurable f)
  (hμ : ReferenceMeasure.measure (α := α) = Measure.count)
  («s.bvar» : β) :
-- imply
  Expectation (ReferenceMeasure.measure.withDensity (fun «a.bvar» ↦ 𝕡.condProb (a, s) («a.bvar», «s.bvar»))) f =
    ∑' «a.bvar» : α, f «a.bvar» * 𝕡.condProb (a, s) («a.bvar», «s.bvar») := by
-- proof
  simp only [Expectation]
  have hcd : Measurable (fun «a.bvar» : α ↦ 𝕡.condProb (a, s) («a.bvar», «s.bvar»)) := by
    unfold Measure.condProb
    fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul _ hcd hf, hμ, lintegral_count]
  exact tsum_congr fun _ ↦ mul_comm _ _


-- created on 2026-09-16
