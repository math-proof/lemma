import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.Basic


/-- The diagonal map is measurable. -/
@[main]
private lemma main
  {α : Type*}
  [MeasurableSpace α] :
-- imply
  Measurable (Function.diag : α → α × α) :=
-- proof
  measurable_diag


-- created on 2026-09-23
