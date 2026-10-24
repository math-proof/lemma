import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_epilogue
open Chapter5 hiding Real
open Chapter5.DedekindCut


/--
[DedekindCut.toReal_isLUB](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_epilogue.lean)
-/
@[path]
private lemma main
  {c: DedekindCut} :
-- imply
  IsLUB c.toSet_Real c.toReal :=
-- proof
  Chapter5.DedekindCut.toReal_isLUB c


-- created on 2026-10-22
