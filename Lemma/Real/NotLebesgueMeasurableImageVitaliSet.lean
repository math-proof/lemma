import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_3
open scoped Pointwise
open VitaliSet


/--
[VitaliSet.nonmeasurable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_3.lean)
-/
@[path]
private lemma main
  :
-- imply
  ¬ LebesgueMeasurable (Real.equiv_EuclideanSpace' '' VitaliSet) :=
-- proof
  VitaliSet.nonmeasurable


-- created on 2026-10-22
