import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval


/--
[midpoint_mem_bisect_snd](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {I : BoundedInterval}
-- given
  (h : I.toSet.Nonempty) :
-- imply
  I.midpoint ∈ (I.bisect.snd).toSet :=
-- proof
  BoundedInterval.midpoint_mem_bisect_snd I h


-- created on 2026-10-22
