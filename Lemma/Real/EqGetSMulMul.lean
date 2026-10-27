import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Chapter6
open Chapter6.Sequence


/--
[Sequence.smul_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a: Sequence}
  {c: ℝ}
  {n:ℤ} :
-- imply
  (c • a) n = c * a n :=
-- proof
  Chapter6.Sequence.smul_eval c n


-- created on 2026-10-22
