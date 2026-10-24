import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open UnsignedSimpleFunction


/--
[UnsignedSimpleFunction.integral_indicator](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: LebesgueMeasurable E) :
-- imply
  (UnsignedSimpleFunction.indicator hE).integ = Lebesgue_measure E :=
-- proof
  UnsignedSimpleFunction.integral_indicator hE


-- created on 2026-10-22
