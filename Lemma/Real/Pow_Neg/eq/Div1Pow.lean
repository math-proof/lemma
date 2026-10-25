import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_6.Part2
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.zpow_neg](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_6.lean)
-/
@[path]
private lemma main
  {x:Chapter5.Real}
  {n:ℕ} :
-- imply
  x^(-n:ℤ) = 1 / (x^n) :=
-- proof
  Chapter5.Real.zpow_neg n


-- created on 2026-10-22
