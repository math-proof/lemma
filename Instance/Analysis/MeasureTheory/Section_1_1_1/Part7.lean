import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Abbrev.Analysis.MeasureTheory.Section_1_1_1.Part3
open BoundedInterval


/-- Enables coercion from {name}`BoundedInterval` to {lean}`Box 1`. -/
instance BoundedInterval.inst_coeBox : Coe (BoundedInterval) (Box 1) where
  coe := toBox

