import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval


/--
[BoundedInterval.set_Icc](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {a b:ℝ} :
-- imply
  (Icc a b : Set ℝ) = .Icc a b :=
-- proof
  BoundedInterval.set_Icc a b


-- created on 2026-10-22
