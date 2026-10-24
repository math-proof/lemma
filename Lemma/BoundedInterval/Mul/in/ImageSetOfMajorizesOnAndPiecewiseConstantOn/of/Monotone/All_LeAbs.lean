import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_8
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[RS_integral_bound_upper_of_bounded](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {M:ℝ}
  {I: BoundedInterval}
  {α:ℝ → ℝ}
-- given
  (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M)
  (hα:Monotone α) :
-- imply
  M * α[I]ₗ ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I} :=
-- proof
  Chapter11.RS_integral_bound_upper_of_bounded h hα


-- created on 2026-10-22
