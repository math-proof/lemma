import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_1
open Finset


/--
[finite_series_of_le](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {m n:ℤ}
  {a b: ℤ → ℝ}
-- given
  (h: ∀ i, m ≤ i → i ≤ n → a i ≤ b i) :
-- imply
  ∑ i ∈ Icc m n, a i ≤ ∑ i ∈ Icc m n, b i :=
-- proof
  Finset.finite_series_of_le h


-- created on 2026-10-20
