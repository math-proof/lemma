import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.Basic


/-- `Prod.snd` is measurable on a product measurable space. -/
@[main]
private lemma main
  {α β : Type*}
  [MeasurableSpace α] [MeasurableSpace β] :
-- imply
  Measurable (Prod.snd : α × β → β) :=
-- proof
  measurable_snd


-- created on 2026-09-23
