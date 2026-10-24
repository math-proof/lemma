import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_1
open BigOperators
open Classical
open Finset


/--
[sum_of_empty](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {n m:ℤ}
  {a: ℤ → ℝ}
-- given
  (h: n < m) :
-- imply
  ∑ i ∈ Icc m n, a i = 0 :=
-- proof
  Finset.sum_of_empty h a


-- created on 2026-10-20
