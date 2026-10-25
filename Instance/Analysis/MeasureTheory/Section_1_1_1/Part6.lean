import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part9
open BoundedInterval


/-- Enables coercion from {lean}`Box d` to {lean}`Set (EuclideanSpace' d)`. -/
instance Box.inst_coeSet {d:ℕ} : Coe (Box d) (Set (EuclideanSpace' d)) where
  coe := toSet

open Classical in
/-- This is to make {name}`Finset`s of {name}`Box`es work properly. -/
noncomputable instance Box.decidableEq {d:ℕ} : DecidableEq (Box d) :=
  fun a b => decidable_of_iff (a.side = b.side) ⟨Box.ext, fun h => h ▸ rfl⟩

