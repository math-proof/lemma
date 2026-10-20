import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_1
open Finset


/--
[shift_finite_series](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {m n k:ℤ}
  {a: ℤ → ℝ} :
-- imply
  ∑ i ∈ Icc m n, a i = ∑ i ∈ Icc (m+k) (n+k), a (i-k) :=
-- proof
  Finset.shift_finite_series a


-- created on 2026-10-20
