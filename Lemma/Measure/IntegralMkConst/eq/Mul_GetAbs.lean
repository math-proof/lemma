import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval
open PiecewiseConstantFunction
@[path]
private lemma main
  {I: BoundedInterval}
  {c: ℝ} :
-- imply
  (PiecewiseConstantFunction.mkConst I c).integral = c * |I|ₗ :=
-- proof
  PiecewiseConstantFunction.integral_mkConst I c


-- created on 2026-10-22
