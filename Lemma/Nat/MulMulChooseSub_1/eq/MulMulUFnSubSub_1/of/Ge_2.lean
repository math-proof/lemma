import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.erdos_379.Part2
open Nat


/--
[binom_eq_2](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_379.lean)
-/
@[path]
private lemma main
  {n k:ℕ}
-- given
  (hk: 2 ≤ k) :
-- imply
  (n.choose k) * k * (k-1) = ((n-2).choose (k-2)) * (n-1) * n :=
-- proof
  binom_eq_2 hk


-- created on 2026-10-22
