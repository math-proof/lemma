import Mathlib.MeasureTheory.MeasurableSpace.Basic
import sympy.Basic


@[main]
private lemma main
  [MeasurableSpace α] [MeasurableSpace β]
  {f g : α → β}
-- given
  (hfg : f = g)
  (hf : Measurable f) :
-- imply
  Measurable g := by
-- proof
  rw [←hfg]
  exact hf


-- created on 2026-09-18
