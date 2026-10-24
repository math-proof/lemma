import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_8
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[RS_integral_bound_upper_nonempty](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
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
  ((PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty :=
-- proof
  Chapter11.RS_integral_bound_upper_nonempty h hα


-- created on 2026-10-22
