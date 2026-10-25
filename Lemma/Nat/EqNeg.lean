import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_4_1.Part8
open Section_4_1


/--
[neg_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean)
-/
@[path]
private lemma main
  {a b:ℕ} :
-- imply
  -(a —— b) = b —— a :=
-- proof
  Section_4_1.Int.neg_eq a b


-- created on 2026-10-20
