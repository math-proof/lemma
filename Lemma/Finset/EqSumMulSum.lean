import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_1
open Finset


/--
[finite_series_of_const_mul](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {f: X' → ℝ}
  {X: Finset X'}
  {c:ℝ} :
-- imply
  ∑ x ∈ X, c * f x = c * ∑ x ∈ X, f x :=
-- proof
  Finset.finite_series_of_const_mul f X c


-- created on 2026-10-20
