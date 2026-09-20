import Mathlib.MeasureTheory.Measure.Count
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace α]
-- given
  (μ : Measure α) :
-- imply
  μ ≪ Measure.count := by
-- proof
  intro s hs
  rw [Measure.count_eq_zero_iff] at hs
  simp [hs]


-- created on 2026-09-20
