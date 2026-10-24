import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval


/--
[mem_bisect_fst_iff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {I : BoundedInterval}
  {x : ℝ}
-- given
  (hx : x ∈ I.toSet) :
-- imply
  x ∈ (I.bisect.fst).toSet ↔ x ≤ I.midpoint :=
-- proof
  BoundedInterval.mem_bisect_fst_iff I x hx


-- created on 2026-10-22
