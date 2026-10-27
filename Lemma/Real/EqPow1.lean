import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_6.Part2
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.zpow_zero](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_6.lean)
-/
@[path]
private lemma main
  {x: Chapter5.Real} :
-- imply
  x ^ (0:ℤ) = 1 :=
-- proof
  Chapter5.Real.zpow_zero x


-- created on 2026-10-22
