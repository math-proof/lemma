import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval


/--
[BoundedInterval.mk'_lclosed](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {a b : ℝ}
  {lclosed uclosed : Bool} :
-- imply
  (mk' a b lclosed uclosed).lclosed = lclosed :=
-- proof
  BoundedInterval.mk'_lclosed a b lclosed uclosed


-- created on 2026-10-22
