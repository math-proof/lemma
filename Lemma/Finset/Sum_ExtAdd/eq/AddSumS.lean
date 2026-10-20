import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_1
open Finset


/--
[finite_series_of_add](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {f g: X' → ℝ}
  {X: Finset X'} :
-- imply
  ∑ x ∈ X, (f + g) x = ∑ x ∈ X, f x + ∑ x ∈ X, g x :=
-- proof
  Finset.finite_series_of_add f g X


-- created on 2026-10-20
