import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  [Countable α]
  [MeasurableSingletonClass α]
  {π : Measure Ω}
  {a : Ω → α} {s : Ω → β}
  {f : α → ENNReal}
-- given
  (hP : PSpace π (a, s))
  (hf : Measurable f)
  (hμ : ReferenceMeasure.measure (α := α) = Measure.count)
  («s.bvar» : β) :
-- imply
  𝔼[a: π](f a | s = «s.bvar») =
    ∑' «a.bvar» : α, f «a.bvar» * ℙ[π](a = «a.bvar» | s = «s.bvar») := by
-- proof
  simp only [Expectation.condRV, expectation_ennreal]
  have hcd : Measurable (fun «a.bvar» : α ↦ π.condProb (a, s) («a.bvar», «s.bvar»)) := by
    unfold Measure.condProb
    fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul _ hcd hf, hμ, lintegral_count]
  exact tsum_congr fun _ ↦ mul_comm _ _


-- created on 2026-09-16
-- updated on 2026-09-20
