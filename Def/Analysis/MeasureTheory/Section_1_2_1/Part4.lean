import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part4
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


namespace Box

/-- Subdivide a box k times, producing a {name}`Finset` of boxes.
    After k iterations, each original box becomes up to 2^(d\*k) sub-boxes. -/
noncomputable def subdivide_iter {d:ℕ} (B: Box d) : ℕ → Finset (Box d)
  | 0 => {B}
  | k+1 => (subdivide_iter B k).biUnion Box.subdivide

end Box
