import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval


/--
[BoundedInterval.set_Ico](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {a b:ℝ} :
-- imply
  (Ico a b : Set ℝ) = .Ico a b :=
-- proof
  BoundedInterval.set_Ico a b


-- created on 2026-10-22
