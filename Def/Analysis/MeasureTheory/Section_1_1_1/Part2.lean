import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part2
open BoundedInterval


/-- A witness for lowerBound of upperBounds -/
def witness_lowerBound_upperBounds {X : Set ℝ} (y : ℝ) (hy : y ∈ X)
    : y ∈ lowerBounds (upperBounds X) := by
  intro u hu; simp [upperBounds] at hu; exact hu hy

/-- A witness for upperBound of lowerBounds -/
def witness_upperBound_lowerBounds {X : Set ℝ} (y : ℝ) (hy : y ∈ X)
    : y ∈ upperBounds (lowerBounds X) := by
  intro u hu; simp [lowerBounds] at hu; exact hu hy

