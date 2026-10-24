import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_8
open Chapter11.BoundedInterval Chapter9
open Chapter11 hiding RS_integ
open Chapter11.PiecewiseConstantOn


/--
[PiecewiseConstantOn.RS_integ_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {P: Partition I}
  {α:ℝ → ℝ}
-- given
  (h: PiecewiseConstantWith f P) :
-- imply
  RS_integ f I α = PiecewiseConstantWith.RS_integ f P α :=
-- proof
  Chapter11.PiecewiseConstantOn.RS_integ_def h α


-- created on 2026-10-22
