import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[zpow_abs](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {x:ℚ}
  {n:ℤ} :
-- imply
  |x|^n = |x^n| :=
-- proof
  Section_4_3.zpow_abs x n


-- created on 2026-10-20
