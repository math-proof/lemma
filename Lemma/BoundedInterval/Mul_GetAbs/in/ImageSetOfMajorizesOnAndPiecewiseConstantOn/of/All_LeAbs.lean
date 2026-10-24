import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_3
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[integral_bound_upper_of_bounded](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_3.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {M:ℝ}
  {I: BoundedInterval}
-- given
  (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) :
-- imply
  M * |I|ₗ ∈ (PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I} :=
-- proof
  Chapter11.integral_bound_upper_of_bounded h


-- created on 2026-10-22
