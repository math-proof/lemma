import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Instance.Analysis.MeasureTheory.Section_1_1_1.Part5
open BoundedInterval


/-- Subset of {name}`BoundedInterval`s is equivalent to subset of their underlying sets. -/
@[simp]
theorem BoundedInterval.subset_iff (I J: BoundedInterval) :
  I ⊆ J ↔ (I:Set ℝ) ⊆ (J:Set ℝ) := by rfl

