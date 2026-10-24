import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_2
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.PiecewiseConstantOn


/--
[PiecewiseConstantOn.integ_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {P: Partition I}
-- given
  (h: PiecewiseConstantWith f P) :
-- imply
  integ f I = PiecewiseConstantWith.integ f P :=
-- proof
  Chapter11.PiecewiseConstantOn.integ_def h


-- created on 2026-10-22
