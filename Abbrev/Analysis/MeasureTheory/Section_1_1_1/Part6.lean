module
public import Def.Analysis.MeasureTheory.Notation.Part2
public import Theorem.Analysis.Section_9_1.Part3
public import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part14
open BoundedInterval
open Pointwise


public section

/-- The elementary measure of a set, defined as the sum of volumes over a disjoint partition. -/
noncomputable abbrev IsElementary.measure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) : ℝ
  := ∑ B ∈ hE.partition.choose, |B|ᵥ

