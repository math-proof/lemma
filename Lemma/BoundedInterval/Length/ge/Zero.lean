import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval


/--
[BoundedInterval.length_nonneg](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval} :
-- imply
  0 ≤ I.length :=
-- proof
  BoundedInterval.length_nonneg I


-- created on 2026-10-22
