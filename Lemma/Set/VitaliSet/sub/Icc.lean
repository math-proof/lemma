import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
open scoped Pointwise


/--
[VitaliSet_subset_unit_interval](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_3.lean)
-/
@[path]
private lemma main
  :
-- imply
  VitaliSet ⊆ Set.Icc 0 1 :=
-- proof
  VitaliSet_subset_unit_interval


-- created on 2026-10-22
