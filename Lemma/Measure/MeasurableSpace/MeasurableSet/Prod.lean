import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.Basic


/-- Product of measurable sets is measurable. -/
@[main]
private lemma main
  {α β : Type*}
  [MeasurableSpace α] [MeasurableSpace β]
  {s : Set α} {t : Set β}
-- given
  (hs : MeasurableSet s)
  (ht : MeasurableSet t) :
-- imply
  MeasurableSet (s ×ˢ t) :=
-- proof
  hs.prod ht


-- created on 2026-09-23
-- updated on 2026-09-26
