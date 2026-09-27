import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.Basic


/-- Restricting a measurable map to a subtype range is measurable. -/
@[main]
private lemma main
  {α β : Type*}
  [MeasurableSpace α] [MeasurableSpace β]
  {p : β → Prop} {f : α → β}
-- given
  (hf : Measurable f)
  {h : ∀ x, p (f x)} :
-- imply
  Measurable fun x => (⟨f x, h x⟩ : Subtype p) :=
-- proof
  hf.subtype_mk


-- created on 2026-09-23
