import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[zpow_add](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {x:ℚ}
  {n m:ℤ}
-- given
  (hx: x ≠ 0) :
-- imply
  x^n * x^m = x^(n+m) :=
-- proof
  Section_4_3.zpow_add x n m hx


-- created on 2026-10-20
