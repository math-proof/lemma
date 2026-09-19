import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main, comm]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {𝕡 : Measure Ω}
  {a : Ω → α} {s : Ω → β}
  {f : α → ENNReal}
-- given
  (hP : PSpace 𝕡 (a, s))
  (hf : Measurable f)
  (c : ENNReal)
  («s.bvar» : β) :
-- imply
  Expectation (ReferenceMeasure.measure.withDensity (fun «a.bvar» ↦ 𝕡.condProb (a, s) («a.bvar», «s.bvar»))) (fun «a.bvar» ↦ c * f «a.bvar») =
    c * Expectation (ReferenceMeasure.measure.withDensity (fun «a.bvar» ↦ 𝕡.condProb (a, s) («a.bvar», «s.bvar»))) f := by
-- proof
  simp only [Expectation]
  exact lintegral_const_mul c hf


-- created on 2026-09-19
