import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.Basic


/-- `Prod.fst` is measurable on a product measurable space. -/
@[main]
private lemma main
  {α β : Type*}
  [MeasurableSpace α] [MeasurableSpace β] :
-- imply
  Measurable (Prod.fst : α × β → α) :=
-- proof
  measurable_fst


-- created on 2026-09-23
