import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.MeasureTheory.Notation.Part2
open Set


/--
[Set.indicator'_of_mem](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Notation.lean)
-/
@[path]
private lemma main
  {E:Set X}
  {x:X}
-- given
  (h: x ∈ E) :
-- imply
  indicator' E x = 1 :=
-- proof
  Set.indicator'_of_mem h


-- created on 2026-10-22
