import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_1
open Chapter11.BoundedInterval
open Chapter11


/--
[BoundedInterval.mem_inter](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {I J: BoundedInterval}
  {x:ℝ} :
-- imply
  x ∈ (I ∩ J : BoundedInterval) ↔ x ∈ I ∧ x ∈ J :=
-- proof
  Chapter11.BoundedInterval.mem_inter I J x


-- created on 2026-10-22
