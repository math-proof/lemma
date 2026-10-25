import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Instance.Analysis.MeasureTheory.Section_1_1_1
open BoundedInterval


/-- The empty {name}`BoundedInterval` coerces to the empty set. -/
@[simp]
theorem BoundedInterval.coe_empty : ((∅ : BoundedInterval):Set ℝ) = ∅ := by
  change toSet (Ioo 0 0) = ∅
  simp only [toSet]
  exact Set.Ioo_self 0

