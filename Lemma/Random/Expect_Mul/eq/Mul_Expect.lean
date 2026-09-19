import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main, comm]
private lemma main
  [MeasurableSpace α]
  {ν : Measure α}
  {f : α → ENNReal}
-- given
  (c : ENNReal)
  (hf : Measurable f) :
-- imply
  Expectation ν (fun a ↦ c * f a) = c * Expectation ν f := by
-- proof
  simp only [Expectation]
  exact lintegral_const_mul c hf


-- created on 2026-09-19
