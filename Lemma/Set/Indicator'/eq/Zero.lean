import Mathlib
import sympy.Basic
import Def.Analysis.MeasureTheory.Notation.Part2
open Set


/--
[Set.indicator'_of_notMem](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Notation.lean)
-/
@[path]
private lemma main
  {E:Set X}
  {x:X}
-- given
  (h: x ∉ E) :
-- imply
  indicator' E x = 0 :=
-- proof
  Set.indicator'_of_notMem h


-- created on 2026-10-22
