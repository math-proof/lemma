import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_2
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.PiecewiseConstantOn


/--
[PiecewiseConstantOn.def](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval} :
-- imply
  PiecewiseConstantOn f I ↔ ∃ P : Partition I, ∀ J ∈ P, ConstantOn f (J:Set ℝ) :=
-- proof
  Chapter11.PiecewiseConstantOn.def f I


-- created on 2026-10-22
