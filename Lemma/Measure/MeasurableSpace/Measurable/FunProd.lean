import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.Basic


/-- A map into a product is measurable iff both components are. -/
@[main, mp, mpr]
private lemma main
  {α β γ : Type*}
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {f : α → β × γ} :
-- imply
  Measurable f ↔ (Measurable fun a => (f a).1) ∧ Measurable fun a => (f a).2 :=
-- proof
  measurable_fun_prod


-- created on 2026-09-23
