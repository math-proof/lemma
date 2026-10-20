import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_1
open Finset


/--
[finite_series_const_mul](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {m n:ℤ}
  {a: ℤ → ℝ}
  {c:ℝ} :
-- imply
  ∑ i ∈ Icc m n, c * a i = c * ∑ i ∈ Icc m n, a i :=
-- proof
  Finset.finite_series_const_mul a c


-- created on 2026-10-20
