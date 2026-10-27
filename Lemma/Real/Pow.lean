import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_6.Part2
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.pow_eq_pow](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_6.lean)
-/
@[path]
private lemma main
  {x: Chapter5.Real}
  {n:ℕ} :
-- imply
  x ^ (n:ℤ) = x ^ n :=
-- proof
  Chapter5.Real.pow_eq_pow x n


-- created on 2026-10-22
