module
public import Def.Analysis.MeasureTheory.Notation.Part2
public import Theorem.Analysis.Section_9_1.Part3
public import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part4
open BoundedInterval


public section

/-- Instance enabling ∈ notation for membership in {name}`BoundedInterval`. -/
instance BoundedInterval.instMembership : Membership ℝ BoundedInterval where
  mem I x := x ∈ (I:Set ℝ)

