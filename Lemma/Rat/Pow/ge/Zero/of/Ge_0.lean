import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[pow_nonneg](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {x:ℚ}
  {n:ℕ}
-- given
  (hx: x ≥ 0) :
-- imply
  x^n ≥ 0 :=
-- proof
  Section_4_3.pow_nonneg n hx


-- created on 2026-10-20
