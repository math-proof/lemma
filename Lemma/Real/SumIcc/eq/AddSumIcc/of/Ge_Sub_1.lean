import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_1
open Finset


/--
[sum_of_nonempty](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {n m:ℤ}
  {a: ℤ → ℝ}
-- given
  (h: n ≥ m-1) :
-- imply
  ∑ i ∈ Icc m (n+1), a i = ∑ i ∈ Icc m n, a i + a (n+1) :=
-- proof
  Finset.sum_of_nonempty h a


-- created on 2026-10-20
