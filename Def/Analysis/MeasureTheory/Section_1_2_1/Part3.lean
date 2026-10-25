import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Instance.Analysis.MeasureTheory.Section_1_2_1
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


namespace Box

/-- Subdivide a box by bisecting each coordinate axis, producing 2^d sub-boxes.
    Each sub-box is formed by taking one half-interval from each coordinate.
    We use {name}`Finset.univ` (all possible d-bit patterns) to enumerate all 2^d combinations. -/
noncomputable def subdivide {d:ℕ} (B: Box d) : Finset (Box d) :=
  -- For each choice ∈ Fin d → Bool (which half to take for each coordinate),
  -- construct a sub-box by taking the left half (if false) or right half (if true)
  Finset.univ.image fun (choice : Fin d → Bool) =>
    { side := fun i =>
        let (left, right) := (B.side i).bisect
        if choice i then right else left }

end Box
