import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_1.Part9
open Chapter5


/--
[from_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  {a:Sequence}
  {n₁ n:ℤ}
-- given
  (hn: n ≥ n₁) :
-- imply
  (a.from n₁) n = a n :=
-- proof
  Chapter5.Sequence.from_eval a hn


-- created on 2026-10-20
