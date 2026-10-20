import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_1
open Finset


/--
[finite_series_of_empty](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {f: X' → ℝ} :
-- imply
  ∑ i ∈ ∅, f i = 0 :=
-- proof
  Finset.finite_series_of_empty f


-- created on 2026-10-20
