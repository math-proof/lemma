import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_2
open Remark_1_3_10


/--
[f_lifted_zero_set_measurable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  :
-- imply
  LebesgueMeasurable {x : EuclideanSpace' 1 | f_lifted x = 0} :=
-- proof
  Remark_1_3_10.f_lifted_zero_set_measurable


-- created on 2026-10-22
