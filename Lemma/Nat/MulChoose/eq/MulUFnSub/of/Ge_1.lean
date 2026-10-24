import Mathlib
import sympy.Basic
import sympy.analysis.Misc.erdos_379
open Nat


/--
[binom_eq](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_379.lean)
-/
@[path]
private lemma main
  {n k:ℕ}
-- given
  (hk: 1 ≤ k) :
-- imply
  (n.choose k) * k = ((n-1).choose (k-1)) * n :=
-- proof
  binom_eq hk


-- created on 2026-10-22
