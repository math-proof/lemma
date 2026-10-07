import Mathlib
import sympy.Basic


@[main]
private lemma main
  {h : ℝ}
  {f : ℝ → ℝ}
  {S : Set ℝ}
  (hf : Measurable f)
  (hS : MeasurableSet S) :
-- imply
  MeasureTheory.volume ((fun x => f x + h) '' S) = MeasureTheory.volume (f '' S) := by
-- proof
  sorry


-- created on 2026-10-07
