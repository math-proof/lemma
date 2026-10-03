import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Lemma.Random.Integral.eq.Expect
import sympy.Basic
open MeasureTheory Random


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  [Countable α] [MeasurableSingletonClass α]
  {π : Measure Ω}
  {a : Ω → α} {s : Ω → β}
  {f : α → ENNReal}
-- given
  (hP : SinglePSpace π (a, s))
  (hf : Measurable f)
  (hμ : ReferenceMeasure.measure (α := α) = Measure.count)
  («s.bvar» : β) :
-- imply
  ∑' «a.bvar» : α, ℙ[π](a = «a.bvar» | s = «s.bvar») * f «a.bvar» =
    Expectation.condRV π a s f «s.bvar» := by
-- proof
  rw [← Integral.eq.Expect hP hf «s.bvar», hμ, lintegral_count]


-- created on 2026-10-01
