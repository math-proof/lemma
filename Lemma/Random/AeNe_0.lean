import Mathlib.MeasureTheory.Measure.MeasureSpace
import sympy.Basic
open MeasureTheory


/--
A countably-valued `X` almost surely takes a value of positive probability.
-/
@[main]
private lemma main
  [MeasurableSpace Ω] [Countable S]
  {π : Measure Ω}
  {X : Ω → S} :
-- imply
  ∀ᵐ ω ∂π, π (X ⁻¹' {X ω}) ≠ 0 := by
-- proof
  rw [ae_iff]
  apply measure_mono_null _ ((measure_biUnion_null_iff (Set.to_countable {x | π (X ⁻¹' {x}) = 0})).2 fun _ hx ↦ hx)
  intro ω hω
  exact Set.mem_biUnion (x := X ω) (not_not.1 hω) rfl


-- created on 2026-10-06
