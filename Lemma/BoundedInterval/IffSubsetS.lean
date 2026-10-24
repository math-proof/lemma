import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval


/--
[BoundedInterval.subset_iff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {I J: BoundedInterval} :
-- imply
  I ⊆ J ↔ (I:Set ℝ) ⊆ (J:Set ℝ) :=
-- proof
  BoundedInterval.subset_iff I J


-- created on 2026-10-22
