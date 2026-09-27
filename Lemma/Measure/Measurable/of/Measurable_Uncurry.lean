import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.Basic
open Function


@[main]
private lemma main
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {f : α → β → γ}
-- given
  (h₀ : Measurable (uncurry f)) :
-- imply
  Measurable f := by
-- proof
  apply measurable_pi_iff.mpr
  intro a
  exact h₀.of_uncurry_right


-- created on 2026-09-26