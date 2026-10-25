import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Instance.Analysis.MeasureTheory.Section_1_1_1.Part6
open BoundedInterval


/-- Lifts a 1-dimensional interval to a 1-dimensional box. -/
@[coe]
abbrev BoundedInterval.toBox (I: BoundedInterval) : Box 1 where
  side := fun _ ↦ I

