import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[pow_mul](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {x:ℚ}
  {m n:ℕ} :
-- imply
  (x^n)^m = x^(n*m) :=
-- proof
  Section_4_3.pow_mul x m n


-- created on 2026-10-20
