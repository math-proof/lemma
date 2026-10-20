import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_1
open Section_4_1


/--
[mul_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean)
-/
@[path]
private lemma main
  {a b c d:ℕ} :
-- imply
  a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) :=
-- proof
  Section_4_1.Int.mul_eq a b c d


-- created on 2026-10-20
