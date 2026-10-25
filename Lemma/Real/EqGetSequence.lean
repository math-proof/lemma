import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Chapter6
open Chapter6.Sequence


/--
[Sequence.eval_coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {n:ℕ}
  {a: ℕ → ℝ} :
-- imply
  (a:Sequence) n = a n :=
-- proof
  Chapter6.Sequence.eval_coe n a


-- created on 2026-10-22
