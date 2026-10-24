import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval


/--
[BoundedInterval.sdiff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {I J: BoundedInterval} :
-- imply
  ∃ K₁ K₂ : BoundedInterval, (I:Set ℝ) \ (J:Set ℝ) = (K₁:Set ℝ) ∪ (K₂:Set ℝ) :=
-- proof
  BoundedInterval.sdiff I J


-- created on 2026-10-22
