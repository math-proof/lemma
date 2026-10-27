import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval


/--
[BoundedInterval.Ioo_subset](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval} :
-- imply
  Ioo I.a I.b ⊆ I :=
-- proof
  BoundedInterval.Ioo_subset I


-- created on 2026-10-22
