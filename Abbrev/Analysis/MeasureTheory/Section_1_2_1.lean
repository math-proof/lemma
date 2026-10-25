import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part10
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


namespace Remark_1_2_8

/-- Unit interval \[0,1\] as a {name}`BoundedInterval` -/
abbrev unit_interval : BoundedInterval := BoundedInterval.Icc 0 1

/-- Unit box in 1D: \[0,1\] lifted to {lean}`Box 1` -/
abbrev unit_box_1D : Box 1 := unit_interval.toBox

end Remark_1_2_8
