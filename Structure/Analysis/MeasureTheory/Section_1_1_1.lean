module

public import Def.Analysis.MeasureTheory.Notation.Part2
public import Theorem.Analysis.Section_9_1.Part3
public import Macro.Analysis.MeasureTheory.Section_1_1_1
public section

open BoundedInterval


/-- A d-dimensional box is a Cartesian product of d bounded intervals. -/
@[ext]
structure Box (d:ℕ) where
  side : Fin d → BoundedInterval

