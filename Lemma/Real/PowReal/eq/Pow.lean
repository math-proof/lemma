import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_6.Part2
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.pow_of_coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_6.lean)
-/
@[path]
private lemma main
  {q: ℚ}
  {n:ℕ} :
-- imply
  (q:Chapter5.Real) ^ n = (q ^ n:ℚ) :=
-- proof
  Chapter5.Real.pow_of_coe q n


-- created on 2026-10-22
