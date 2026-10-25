import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Def.Analysis.MeasureTheory.Section_1_1_1
open BoundedInterval


/-- Enables coercion from {name}`BoundedInterval` to {lean}`Set ℝ`. -/
instance BoundedInterval.inst_coeSet : Coe BoundedInterval (Set ℝ) where
  coe := toSet

/-- The empty {name}`BoundedInterval` is represented as the degenerate open interval (0,0). -/
instance BoundedInterval.instEmpty : EmptyCollection BoundedInterval where
  emptyCollection := Ioo 0 0

