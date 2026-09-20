import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main, comm]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure γ]
  {π : Measure Ω}
  {a : Ω → α} {s : Ω → γ}
  {f : α → ENNReal}
-- given
  (hP : PSpace π (a, s))
  (hf : Measurable f)
  (c : ENNReal)
  («s.bvar» : γ) :
-- imply
  𝔼[a: π](c * f a | s = «s.bvar») = c * 𝔼[a: π](f a | s = «s.bvar») := by
-- proof
  simp only [Expectation.condRV, expectation_ennreal]
  exact lintegral_const_mul c hf


-- created on 2026-09-19
-- updated on 2026-09-20
