import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval


/--
[BoundedInterval.mem_iff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {x:ℝ} :
-- imply
  x ∈ I ↔ x ∈ (I:Set ℝ) :=
-- proof
  BoundedInterval.mem_iff I x


-- created on 2026-10-22
