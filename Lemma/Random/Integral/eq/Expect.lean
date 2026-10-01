import Lemma.Random.ExpectCond.eq.Integral_Mul_ProbCond
import sympy.Basic
open MeasureTheory Random


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω}
  {a : Ω → α} {s : Ω → β}
  {f : α → ENNReal}
-- given
  (hP : SinglePSpace π (a, s))
  (hf : Measurable f)
  («s.bvar» : β) :
-- imply
  ∫⁻ «a.bvar», ℙ[π](a = «a.bvar» | s = «s.bvar») * f «a.bvar» ∂ReferenceMeasure.measure = 𝔼[a: π](f a | s = «s.bvar») := by
-- proof
  rw [ExpectCond.eq.Integral_Mul_ProbCond hP hf]
  apply lintegral_congr fun _ => mul_comm _ _


-- created on 2026-10-01
