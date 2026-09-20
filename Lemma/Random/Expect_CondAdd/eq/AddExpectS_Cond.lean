import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main, comm]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω}
  {a : Ω → α} {s : Ω → β}
  {f g : α → ENNReal}
-- given
  (hP : PSpace π (a, s))
  (hf : Measurable f)
  («s.bvar» : β) :
-- imply
  𝔼[a: π](f a + g a | s = «s.bvar») =
    𝔼[a: π](f a | s = «s.bvar») + 𝔼[a: π](g a | s = «s.bvar») := by
-- proof
  simp only [Expectation.condRV, expectation_ennreal]
  exact lintegral_add_left hf g


-- created on 2023-03-24
-- updated on 2026-09-20
