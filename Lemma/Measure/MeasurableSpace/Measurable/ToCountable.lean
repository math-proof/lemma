import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.Basic


/-- Maps into a countable space are measurable when singleton preimages are. -/
@[main]
private lemma main
  {α β : Type*}
  [MeasurableSpace α] [Countable α] [MeasurableSpace β]
  {f : β → α}
-- given
  (h : ∀ y, MeasurableSet (f ⁻¹' {f y})) :
-- imply
  Measurable f :=
-- proof
  measurable_to_countable h


-- created on 2026-09-23
