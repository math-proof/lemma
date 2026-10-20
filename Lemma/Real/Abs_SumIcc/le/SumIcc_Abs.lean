import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_1
open Finset


/--
[abs_finite_series_le](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {m n:ℤ}
  {a: ℤ → ℝ} :
-- imply
  |∑ i ∈ Icc m n, a i| ≤ ∑ i ∈ Icc m n, |a i| :=
-- proof
  Finset.abs_finite_series_le a


-- created on 2026-10-20
