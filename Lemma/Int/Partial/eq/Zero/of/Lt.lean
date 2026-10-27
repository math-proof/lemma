import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_7_2.Part5
open Chapter7


/--
[partial_of_lt](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_2.lean)
-/
@[path]
private lemma main
  {s : Series}
  {N:ℤ}
-- given
  (h: N < s.m) :
-- imply
  s.partial N = 0 :=
-- proof
  Chapter7.Series.partial_of_lt h


-- created on 2026-10-20
