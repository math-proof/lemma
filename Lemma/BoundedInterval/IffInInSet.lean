import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_1
open Chapter11.BoundedInterval
open Chapter11


/--
[BoundedInterval.mem_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {x:ℝ} :
-- imply
  x ∈ I ↔ x ∈ (I:Set ℝ) :=
-- proof
  Chapter11.BoundedInterval.mem_iff I x


-- created on 2026-10-22
