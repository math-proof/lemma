import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_1
open Chapter6
open Chapter6.Sequence


/--
[Sequence.sub_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a b: Sequence}
  {n:ℤ} :
-- imply
  (a - b) n = a n - b n :=
-- proof
  Chapter6.Sequence.sub_eval n


-- created on 2026-10-22
