import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Theorem.Analysis.MeasureTheory.Section_1_1_1
open BoundedInterval


open Classical in
/-- This is to make {name}`Finset`s of {name}`BoundedInterval`s work properly -/
noncomputable instance BoundedInterval.decidableEq : DecidableEq BoundedInterval := instDecidableEqOfLawfulBEq

