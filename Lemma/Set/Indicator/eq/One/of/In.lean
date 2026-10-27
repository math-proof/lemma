import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open EReal


/--
[EReal.indicator_of_mem](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {A: Set X}
  {x:X}
-- given
  (h: x ∈ A) :
-- imply
  EReal.indicator A x = 1 :=
-- proof
  EReal.indicator_of_mem h


-- created on 2026-10-22
