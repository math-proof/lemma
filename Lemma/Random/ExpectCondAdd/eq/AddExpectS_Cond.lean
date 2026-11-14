import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorem.Probability.CondExpectation
import Initialize.Tactic.Attr.Basic
import Theorem.Probability.JointRv.AsRV
open MeasureTheory


@[path, comm]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [StandardBorelSpace α] [Nonempty α]
  [ReferenceMeasure β]
  {π : Measure Ω} [IsFiniteMeasure π]
  {a : Ω → α} {s : Ω → β}
  {f g : α → ENNReal}
-- given
  (hf : Measurable f)
  («\sf{s}» : β) :
-- imply
  𝔼[a: π](f a + g a | s = «\sf{s}») =
    𝔼[a: π](f a | s = «\sf{s}») + 𝔼[a: π](g a | s = «\sf{s}») := by
-- proof
  simp only [Expectation.asRV_function, Expectation.condEval, expectation_ennreal]
  exact lintegral_add_left hf g


-- created on 2023-03-24
-- updated on 2026-11-13
