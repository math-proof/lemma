import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval


/--
[midpoint_mem_bisect_fst](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {I : BoundedInterval}
-- given
  (h : I.toSet.Nonempty) :
-- imply
  I.midpoint ∈ (I.bisect.fst).toSet :=
-- proof
  BoundedInterval.midpoint_mem_bisect_fst I h


-- created on 2026-10-22
