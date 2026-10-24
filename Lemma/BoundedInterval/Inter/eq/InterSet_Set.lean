import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval


/--
[BoundedInterval.inter_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {I J: BoundedInterval} :
-- imply
  (I ∩ J : BoundedInterval) = (I:Set ℝ) ∩ (J:Set ℝ) :=
-- proof
  BoundedInterval.inter_eq I J


-- created on 2026-10-22
