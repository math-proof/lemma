import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval


/--
[BoundedInterval.interior_closure_subset_closure_interior](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {I : BoundedInterval} :
-- imply
  interior (closure (I : Set ℝ)) ⊆ closure (interior (I : Set ℝ)) :=
-- proof
  BoundedInterval.interior_closure_subset_closure_interior I


-- created on 2026-10-22
