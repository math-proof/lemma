import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[Box.toSet_nonempty_of_IsDyadic](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {B : Box d}
-- given
  (hB : B.IsDyadic) :
-- imply
  B.toSet.Nonempty :=
-- proof
  Box.toSet_nonempty_of_IsDyadic hB


-- created on 2026-10-22
