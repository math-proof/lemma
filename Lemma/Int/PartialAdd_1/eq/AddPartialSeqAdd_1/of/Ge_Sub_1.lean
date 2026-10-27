import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_7_2.Part5
open Chapter7


/--
[partial_succ](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_2.lean)
-/
@[path]
private lemma main
  {s : Series}
  {N:ℤ}
-- given
  (h: N ≥ s.m-1) :
-- imply
  s.partial (N+1) = s.partial N + s.seq (N+1) :=
-- proof
  Chapter7.Series.partial_succ s h


-- created on 2026-10-20
