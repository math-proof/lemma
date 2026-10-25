import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Structure.Analysis.MeasureTheory.Section_1_1_1
open BoundedInterval


/-- Coerces a {name}`Box` to its underlying set in d-dimensional Euclidean space. -/
@[coe]
def Box.toSet {d:ℕ} (B: Box d) : Set (EuclideanSpace' d) :=
  {x | ∀ i, x i ∈ (B.side i : Set ℝ)}

