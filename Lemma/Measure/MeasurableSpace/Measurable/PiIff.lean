import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.Basic


/-- A map into a pi-type is measurable iff every coordinate is. -/
@[main, mp, mpr]
private lemma main
  {α δ : Type*} {X : δ → Type*}
  [MeasurableSpace α] [∀ a, MeasurableSpace (X a)]
  {g : α → ∀ a, X a} :
-- imply
  Measurable g ↔ ∀ a, Measurable fun x => g x a :=
-- proof
  measurable_pi_iff


-- created on 2026-09-23
