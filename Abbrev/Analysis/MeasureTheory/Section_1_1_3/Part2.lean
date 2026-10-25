import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
import Structure.Analysis.MeasureTheory.Section_1_1_3.Part2
open BoundedInterval

@[ext]
/-!
# Introduction to Measure Theory, Section 1.1.3: Connections with the Riemann integral

A companion to Section 1.1.3 of the book "An introduction to Measure Theory".

-/


-- Two functions agree if they are equal on the interval I.
abbrev PiecewiseConstantFunction.agreesWith {I: BoundedInterval} (F: PiecewiseConstantFunction I) (f: ℝ → ℝ) : Prop := I.toSet.EqOn f F.f

