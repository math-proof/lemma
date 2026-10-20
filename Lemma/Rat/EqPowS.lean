import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[zpow_mul](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {x:ℚ}
  {n m:ℤ} :
-- imply
  (x^n)^m = x^(n*m) :=
-- proof
  Section_4_3.zpow_mul x n m


-- created on 2026-10-20
