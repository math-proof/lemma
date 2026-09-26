import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.Basic


/-- `Prod.swap` is measurable. -/
@[main]
private lemma main
  {α β : Type*}
  [MeasurableSpace α] [MeasurableSpace β] :
-- imply
  Measurable (Prod.swap : α × β → β × α) :=
-- proof
  measurable_swap


-- created on 2026-09-23
