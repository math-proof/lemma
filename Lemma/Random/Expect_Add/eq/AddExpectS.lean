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
  {f g : α → ENNReal}
-- given
  (hP : PSpace π a)
  (hf : Measurable f) :
-- imply
  𝔼[a: π](f a + g a) = 𝔼[a: π](f a) + 𝔼[a: π](g a) := by
-- proof
  simp only [Expectation.ofRV, expectation_ennreal]
  exact lintegral_add_left hf g


-- created on 2023-03-24
-- updated on 2026-09-20
