import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_11_2.Part6
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.PiecewiseConstantWith


/--
[PiecewiseConstantWith.integ_congr](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean)
-/
@[path]
private lemma main
  {f g:ℝ → ℝ}
  {I: BoundedInterval}
  {P: Partition I}
-- given
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) :
-- imply
  integ f P = integ g P :=
-- proof
  Chapter11.PiecewiseConstantWith.integ_congr h


-- created on 2026-10-22
