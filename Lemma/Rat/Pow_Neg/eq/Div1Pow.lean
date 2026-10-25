import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_4_3.Part2
open Section_4_3


/--
[zpow_neg](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {x:ℚ}
  {n:ℕ} :
-- imply
  x^(-(n:ℤ)) = 1/(x^n) :=
-- proof
  Section_4_3.zpow_neg x n


-- created on 2026-10-20
