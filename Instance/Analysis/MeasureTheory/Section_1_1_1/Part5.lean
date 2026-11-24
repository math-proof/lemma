module
public import Def.Analysis.MeasureTheory.Notation.Part2
public import Theorem.Analysis.Section_9_1.Part3
public import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part5
open BoundedInterval


public section

/-- Instance enabling ⊆ notation for {name}`BoundedInterval`s. -/
instance BoundedInterval.instSubset : HasSubset BoundedInterval where
  Subset I J := ∀ x, x ∈ I → x ∈ J

