import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval


/--
[BoundedInterval.set_Ioc](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {a b:ℝ} :
-- imply
  (Ioc a b : Set ℝ) = .Ioc a b :=
-- proof
  BoundedInterval.set_Ioc a b


-- created on 2026-10-22
