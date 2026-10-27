import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_epilogue.Part5
open Chapter5 hiding Real
open Chapter5.DedekindCut


/--
[DedekindCut.toR_isLUB](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_epilogue.lean)
-/
@[path]
private lemma main
  {c: DedekindCut} :
-- imply
  IsLUB c.toSet_R c.toR :=
-- proof
  Chapter5.DedekindCut.toR_isLUB c


-- created on 2026-10-22
