import Lemma.Random.ExpectCond.eq.Integral_Mul_ProbCond
open MeasureTheory Random


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
  ∫⁻ «\sf{a}», ℙ[π](a = «\sf{a}» | s = «\sf{s}») * f «\sf{a}» ∂ReferenceMeasure.measure = Expectation.condRV π a s f «\sf{s}» := by
-- proof
  rw [ExpectCond.eq.Integral_Mul_ProbCond hP hf]
  apply lintegral_congr fun _ => mul_comm _ _


-- created on 2023-04-02
-- updated on 2026-11-02
