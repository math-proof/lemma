import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_4_1.Part8
open Section_4_1


/--
[add_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean)
-/
@[path]
private lemma main
  {a b c d:ℕ} :
-- imply
  a —— b + c —— d = (a+c)——(b+d) :=
-- proof
  Section_4_1.Int.add_eq a b c d


-- created on 2026-10-20
