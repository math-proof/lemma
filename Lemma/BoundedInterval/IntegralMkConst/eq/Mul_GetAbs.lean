import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_3
open BoundedInterval
open PiecewiseConstantFunction


/--
[integral_mkConst](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {c: ℝ} :
-- imply
  (PiecewiseConstantFunction.mkConst I c).integral = c * |I|ₗ :=
-- proof
  PiecewiseConstantFunction.integral_mkConst I c


-- created on 2026-10-22
