module
public import Def.Analysis.MeasureTheory.Notation.Part2
public import Theorem.Analysis.Section_9_1.Part3
public import Structure.Analysis.MeasureTheory.Section_1_1_1
open BoundedInterval


public section

/-- Coerces a {name}`Box` to its underlying set in d-dimensional Euclidean space. -/
@[coe]
def Box.toSet {d:ℕ} (B: Box d) : Set (EuclideanSpace' d) :=
  {x | ∀ i, x i ∈ (B.side i : Set ℝ)}

