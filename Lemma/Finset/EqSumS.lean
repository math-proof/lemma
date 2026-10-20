import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_1
open Finset


/--
[finite_series_of_fintype](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {f: X' → ℝ}
  {X: Finset X'} :
-- imply
  ∑ x ∈ X, f x = ∑ x:X, f x.val :=
-- proof
  Finset.finite_series_of_fintype f X


-- created on 2026-10-20
