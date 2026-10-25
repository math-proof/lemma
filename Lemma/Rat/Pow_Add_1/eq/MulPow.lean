import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_4_3.Part2
open Section_4_3


/--
[pow_succ](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {x:ℚ}
  {n:ℕ} :
-- imply
  x^(n+1) = x^n * x :=
-- proof
  Section_4_3.pow_succ x n


-- created on 2026-10-20
