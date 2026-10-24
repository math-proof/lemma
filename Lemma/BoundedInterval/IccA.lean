import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval


/--
[BoundedInterval.subset_Icc](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval} :
-- imply
  I ⊆ Icc I.a I.b :=
-- proof
  BoundedInterval.subset_Icc I


-- created on 2026-10-22
