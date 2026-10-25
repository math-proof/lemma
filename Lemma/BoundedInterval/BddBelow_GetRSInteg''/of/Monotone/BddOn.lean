import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_11_8.Part7
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[RS_integral_bound_below](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {α:ℝ → ℝ}
-- given
  (h: BddOn f I)
  (hα: Monotone α) :
-- imply
  BddBelow ((PiecewiseConstantOn.RS_integ · I α) ''
      {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}) :=
-- proof
  Chapter11.RS_integral_bound_below h hα


-- created on 2026-10-22
