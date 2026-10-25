import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval


/--
[BoundedInterval.coe_of_box](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {I:BoundedInterval} :
-- imply
  (I:Box 1).toSet = Real.equiv_EuclideanSpace' '' I.toSet :=
-- proof
  BoundedInterval.coe_of_box I


-- created on 2026-10-22
