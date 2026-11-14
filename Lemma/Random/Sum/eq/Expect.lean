import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Lemma.Random.Integral.eq.Expect
open MeasureTheory Random


@[path]
private lemma main
  [MeasurableSpace Ω]
  [μ : ReferenceMeasure α] [ReferenceMeasure β]
  [Countable α] [MeasurableSingletonClass α]
  {π : Measure Ω}
  {a : Ω → α} {s : Ω → β}
  {f : α → ENNReal}
-- given
  (hP : SinglePSpace π (a, s))
  (hf : Measurable f)
  (hμ : μ.measure = Measure.count)
  («\sf{s}» : β) :
-- imply
  ∑' «\sf{a}» : α, ℙ[π](a = «\sf{a}» | s = «\sf{s}») * f «\sf{a}» =
    Expectation.condRV π a s f «\sf{s}» := by
-- proof
  rw [← Integral.eq.Expect hP hf «\sf{s}», hμ, lintegral_count]


-- created on 2023-04-02
-- updated on 2026-11-14
