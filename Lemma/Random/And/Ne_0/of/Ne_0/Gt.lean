import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import sympy.Basic
open MeasureTheory


/--
A positive-probability event sits inside each of two larger events, so both larger events are positive.
This is the prefix/suffix split of a joint atom `x[:m] = v`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {s t u : Set Ω}
-- given
  (h₀ : s ⊆ t)
  (h₁ : s ⊆ u)
  (h₂ : π s ≠ 0) :
-- imply
  π t ≠ 0 ∧ π u ≠ 0 := by
-- proof
  constructor
  · exact ne_of_gt (lt_of_lt_of_le (pos_of_ne_zero h₂) (measure_mono h₀))
  · exact ne_of_gt (lt_of_lt_of_le (pos_of_ne_zero h₂) (measure_mono h₁))


-- created on 2026-10-11
-- updated on 2026-10-17
