module
public import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
public import Theorem.Analysis.Misc.RealERealENNReal
public import Theorem.Analysis.Misc.Combinatorics
public import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part14
open BoundedInterval


public section

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/
/-- For a point x, the unique dyadic cube at scale n containing x. -/
noncomputable def dyadicCubeContaining {d:ℕ} (n:ℤ) (x : EuclideanSpace' d) : Box d :=
  DyadicCube n (fun i => ⌊x i * 2^n⌋)

