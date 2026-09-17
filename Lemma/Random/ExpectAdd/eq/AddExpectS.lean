import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main, comm]
private lemma main
  [MeasurableSpace α]
  {ν : Measure α}
  {f g : α → ENNReal}
-- given
  (hf : Measurable f) :
-- imply
  Expectation ν (f + g) = Expectation ν f + Expectation ν g := by
-- proof
  simp only [Expectation, Pi.add_apply]
  exact lintegral_add_left hf g


-- created on 2026-09-17
