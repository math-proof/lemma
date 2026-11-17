import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorem.Probability.CondExpectation
open MeasureTheory


/--
| attributes | lemma |
| :---: | :---: |
| path | Random.ExpectCondMul.eq.Mul_ExpectCond |
| comm | Random.Mul_ExpectCond.eq.ExpectCondMul |
-/
@[path, comm]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  [MeasurableSpace γ]
  {π : Measure Ω} [IsFiniteMeasure π]
  {a : Ω → α} {s : Ω → γ}
  {f : α → ENNReal}
-- given
  (hf : Measurable f)
  (c : ENNReal)
  («\sf{s}» : γ) :
-- imply
  𝔼[a: π](c * f a | s = «\sf{s}») = c * 𝔼[a: π](f a | s = «\sf{s}») := by
-- proof
  simp only [Expectation.asRV_function, Expectation.condEval, expectation_ennreal]
  exact lintegral_const_mul c hf


-- created on 2026-09-19
-- updated on 2026-11-15
