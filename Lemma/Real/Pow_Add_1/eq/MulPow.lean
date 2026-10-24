import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_6
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.pow_succ](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_6.lean)
-/
@[path]
private lemma main
  {x: Chapter5.Real}
  {n:ℕ} :
-- imply
  x ^ (n+1) = (x ^ n) * x :=
-- proof
  Chapter5.Real.pow_succ x n


-- created on 2026-10-22
