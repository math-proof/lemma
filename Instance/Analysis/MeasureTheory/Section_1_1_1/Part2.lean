module
public import Def.Analysis.MeasureTheory.Notation.Part2
public import Theorem.Analysis.Section_9_1.Part3
public import Theorem.Analysis.MeasureTheory.Section_1_1_1
open BoundedInterval
open Classical in


public section

/-- This is to make {name}`Finset`s of {name}`BoundedInterval`s work properly -/
noncomputable instance BoundedInterval.decidableEq : DecidableEq BoundedInterval := instDecidableEqOfLawfulBEq

