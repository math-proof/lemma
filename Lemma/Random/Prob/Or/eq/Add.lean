import Mathlib.MeasureTheory.Measure.Real
import sympy.Basic

open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {s t : Set Ω}
-- given
  (_ : MeasurableSet s)
  (ht : MeasurableSet t) :
-- imply
  P.real (s ∪ t) = P.real s + P.real t - P.real (s ∩ t) := by
-- proof
  have h := measureReal_union_add_inter₀ ht.nullMeasurableSet (μ := P)
  linarith


-- created on 2026-10-07
