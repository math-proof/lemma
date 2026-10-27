import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open IsElementary


/--
[iUnion_boxes](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  [Fintype ι]
  {d : ℕ}
  {B : ι → Box d} :
-- imply
  IsElementary (⋃ i, (B i).toSet) :=
-- proof
  IsElementary.iUnion_boxes B


-- created on 2026-10-22
