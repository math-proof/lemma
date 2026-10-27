import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_7_2.Part5
open Chapter7


/--
[convergesTo_uniq](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_2.lean)
-/
@[path]
private lemma main
  {s : Series}
  {L L':ℝ}
-- given
  (h: s.convergesTo L)
  (h': s.convergesTo L') :
-- imply
  L = L' :=
-- proof
  Chapter7.Series.convergesTo_uniq h h'


-- created on 2026-10-20
