import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_3
open BoundedInterval
open PiecewiseConstantFunction


/--
[integral_neg](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {g: PiecewiseConstantFunction I} :
-- imply
  g.neg.integral = -g.integral :=
-- proof
  PiecewiseConstantFunction.integral_neg g


-- created on 2026-10-22
