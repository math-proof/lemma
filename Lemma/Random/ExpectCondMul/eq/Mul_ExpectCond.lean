import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorem.Probability.CondExpectation
import Initialize.Tactic.Attr.Basic
open MeasureTheory


@[path, comm]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α]
  {π : Measure Ω}
  {a : Ω → α} {s : Ω → γ}
  {f : α → ENNReal}
-- given
  (hf : Measurable f)
  (c : ENNReal)
  («\sf{s}» : γ) :
-- imply
  𝔼[a: π](c * f a | s = «\sf{s}») = c * 𝔼[a: π](f a | s = «\sf{s}») := by
-- proof
  simp only [Expectation.asRV_function, Expectation.condEvent, expectation_ennreal]
  exact lintegral_const_mul c hf


-- created on 2026-09-19
-- updated on 2026-11-02
