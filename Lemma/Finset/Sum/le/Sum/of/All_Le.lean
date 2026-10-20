import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_1
open Finset


/--
[finite_series_of_le'](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {f g: X' → ℝ}
  {X: Finset X'}
-- given
  (h: ∀ x ∈ X, f x ≤ g x) :
-- imply
  ∑ x ∈ X, f x ≤ ∑ x ∈ X, g x :=
-- proof
  Finset.finite_series_of_le' f g X h


-- created on 2026-10-20
