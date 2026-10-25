import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval
open PiecewiseConstantFunction


/--
[integral_mono'](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {g h: PiecewiseConstantFunction I}
-- given
  (h_pointwise: ∀ x ∈ I.toSet, g.f x ≤ h.f x) :
-- imply
  g.integral ≤ h.integral :=
-- proof
  PiecewiseConstantFunction.integral_mono' g h h_pointwise


-- created on 2026-10-22
