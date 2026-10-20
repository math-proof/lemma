import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_1
open Chapter5


/--
[eval_coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  {n:ℕ}
  {a: ℕ → ℚ} :
-- imply
  (a:Sequence) n = a n :=
-- proof
  Chapter5.Sequence.eval_coe n a


-- created on 2026-10-20
