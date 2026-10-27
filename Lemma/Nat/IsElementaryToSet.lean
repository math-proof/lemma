import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open IsElementary


/--
[IsElementary.box](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d} :
-- imply
  IsElementary B.toSet :=
-- proof
  IsElementary.box B


-- created on 2026-10-22
