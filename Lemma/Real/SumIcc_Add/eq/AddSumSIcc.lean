import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_1
open Finset


/--
[finite_series_add](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {m n:ℤ}
  {a b: ℤ → ℝ} :
-- imply
  ∑ i ∈ Icc m n, (a i + b i) = ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc m n, b i :=
-- proof
  Finset.finite_series_add a b


-- created on 2026-10-20
