import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorem.Probability.CondExpectation
import Initialize.Tactic.Attr.Basic
open MeasureTheory


@[path, comm]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω}
  {a : Ω → α} {s : Ω → β}
  {f g : α → ENNReal}
-- given
  (hf : Measurable f)
  («\sf{s}» : β) :
-- imply
  𝔼[a: π](f a + g a | s = «\sf{s}») =
    𝔼[a: π](f a | s = «\sf{s}») + 𝔼[a: π](g a | s = «\sf{s}») := by
-- proof
  simp only [Expectation.asRV_function, Expectation.condEvent, expectation_ennreal]
  exact lintegral_add_left hf g


-- created on 2023-03-24
-- updated on 2026-11-02
