module
public import Def.Analysis.MeasureTheory.Notation.Part2
public import Theorem.Analysis.Section_9_1.Part3
public import Def.Analysis.MeasureTheory.Section_1_1_1.Part3
open BoundedInterval


public section

@[simp]
theorem Box.mem_toSet {d:ℕ} {B: Box d} {x : EuclideanSpace' d} :
    x ∈ B.toSet ↔ ∀ i, x i ∈ (B.side i : Set ℝ) := Iff.rfl

