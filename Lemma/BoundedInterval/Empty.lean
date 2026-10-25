import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval


/--
[BoundedInterval.coe_empty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  :
-- imply
  ((∅ : BoundedInterval):Set ℝ) = ∅ :=
-- proof
  BoundedInterval.coe_empty


-- created on 2026-10-22
