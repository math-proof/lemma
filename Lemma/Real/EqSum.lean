import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_7_2.Part5
open Chapter7


/--
[sum_of_converges](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_2.lean)
-/
@[path]
private lemma main
  {s : Series}
  {L:ℝ}
-- given
  (h: s.convergesTo L) :
-- imply
  s.sum = L :=
-- proof
  Chapter7.Series.sum_of_converges h


-- created on 2026-10-20
