module
public import Def.Analysis.MeasureTheory.Notation.Part2
public import Theorem.Analysis.Section_9_1.Part3
public import Inductive.Analysis.MeasureTheory.Section_1_1_1
open BoundedInterval


public section

/-- Coerces a {name}`BoundedInterval` to its underlying set of real numbers. -/
@[coe]
def BoundedInterval.toSet (I: BoundedInterval) : Set ℝ := match I with
  | Ioo a b => .Ioo a b
  | Icc a b => .Icc a b
  | Ioc a b => .Ioc a b
  | Ico a b => .Ico a b

