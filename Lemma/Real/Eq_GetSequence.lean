import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Chapter6
open Chapter6.Chapter5


/--
[Chapter5.coe_sequence_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a: Chapter5.Sequence}
  {n:ℤ} :
-- imply
  (a:Sequence) n = (a n:ℝ) :=
-- proof
  Chapter6.Chapter5.coe_sequence_eval a n


-- created on 2026-10-22
