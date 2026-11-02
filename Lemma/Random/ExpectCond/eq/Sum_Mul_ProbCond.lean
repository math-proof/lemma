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
  («\sf{s}» : β) :
-- imply
  Expectation.condRV π a s f «\sf{s}» =
    ∑' «\sf{a}» : α, f «\sf{a}» * ℙ[π](a = «\sf{a}» | s = «\sf{s}») := by
-- proof
  simp only [Expectation.condRV, expectation_ennreal]
  have hcd : Measurable (fun «\sf{a}» : α ↦ π.condProb (a, s) («\sf{a}», «\sf{s}»)) := by
    unfold Measure.condProb
    fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul _ hcd hf, hμ, lintegral_count]
  exact tsum_congr fun _ ↦ mul_comm _ _


-- created on 2026-09-16
-- updated on 2026-11-02
