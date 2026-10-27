import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.WithDensity
import Syntax.Probability.JointRv.Part6
import Initialize.Tactic.Attr.Basic
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  [Countable α]
  [MeasurableSingletonClass α]
  {π : Measure Ω}
  {a : Ω → α} {s : Ω → β}
  {f : α → ENNReal}
-- given
  (hP : SinglePSpace π (a, s))
  (hf : Measurable f)
  (hμ : ReferenceMeasure.measure (α := α) = Measure.count)
  («s.bvar» : β) :
-- imply
  Expectation.condRV π a s f «s.bvar» =
    ∑' «a.bvar» : α, f «a.bvar» * ℙ[π](a = «a.bvar» | s = «s.bvar») := by
-- proof
  simp only [Expectation.condRV, expectation_ennreal]
  have hcd : Measurable (fun «a.bvar» : α ↦ π.condProb (a, s) («a.bvar», «s.bvar»)) := by
    unfold Measure.condProb
    fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul _ hcd hf, hμ, lintegral_count]
  exact tsum_congr fun _ ↦ mul_comm _ _


-- created on 2026-09-16
-- updated on 2026-10-26
