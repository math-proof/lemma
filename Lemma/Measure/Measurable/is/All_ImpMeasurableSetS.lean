import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Initialize.Tactic.Attr.Basic


/--
`f` is measurable if and only if the preimage of every measurable set is measurable.
-/
@[path, mp, mpr]
private lemma main
  [MeasurableSpace α] [MeasurableSpace β]
  {f : α → β} :
-- imply
  Measurable f ↔ ∀ (B : β → Prop), MeasurableSet B → MeasurableSet (f ⁻¹' B) :=
-- proof
  Iff.rfl


-- created on 2026-11-18
