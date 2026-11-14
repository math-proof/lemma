import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval
open PiecewiseConstantFunction
@[path]
private lemma main
  {I: BoundedInterval}
  {g: PiecewiseConstantFunction I} :
-- imply
  ∃ (h: PiecewiseConstantOn g.f I), h.integral = g.integral :=
-- proof
  PiecewiseConstantFunction.to_PiecewiseConstantOn g


-- created on 2026-10-22
