import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main, comm]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {a : Ω → α}
  {f : α → ENNReal}
-- given
  (hP : PSpace π a)
  (hf : Measurable f)
  (c : ENNReal) :
-- imply
  𝔼[a: π](c * f a) = c * 𝔼[a: π](f a) := by
-- proof
  simp only [Expectation.ofRV, expectation_ennreal]
  exact lintegral_const_mul c hf


-- created on 2023-03-24
-- updated on 2026-09-20
