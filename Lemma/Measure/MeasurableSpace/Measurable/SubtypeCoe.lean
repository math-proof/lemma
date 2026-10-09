import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.Basic


/-- Coercion out of a measurable subtype is measurable. -/
@[path]
private lemma main
  {α : Type*}
  [MeasurableSpace α]
  {p : α → Prop} :
-- imply
  Measurable ((↑) : Subtype p → α) :=
-- proof
  measurable_subtype_coe


-- created on 2026-09-23
