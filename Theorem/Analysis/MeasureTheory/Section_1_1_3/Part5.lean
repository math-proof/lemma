import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
import Def.Analysis.MeasureTheory.Section_1_1_3.Part5
open BoundedInterval

@[ext]
/-!
# Introduction to Measure Theory, Section 1.1.3: Connections with the Riemann integral

A companion to Section 1.1.3 of the book "An introduction to Measure Theory".

-/


namespace PiecewiseConstantFunction

/-- Helper: The integral of a constant piecewise constant function -/
lemma integral_mkConst (I: BoundedInterval) (c: ℝ) :
    (PiecewiseConstantFunction.mkConst I c).integral = c * |I|ₗ := by
  unfold PiecewiseConstantFunction.integral PiecewiseConstantFunction.mkConst
  simp [Finset.sum_singleton]

end PiecewiseConstantFunction
