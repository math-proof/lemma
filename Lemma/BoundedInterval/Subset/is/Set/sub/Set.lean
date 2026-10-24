import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_1
open Chapter11.BoundedInterval
open Chapter11


/--
[BoundedInterval.subset_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {I J: BoundedInterval} :
-- imply
  I ⊆ J ↔ (I:Set ℝ) ⊆ (J:Set ℝ) :=
-- proof
  Chapter11.BoundedInterval.subset_iff I J


-- created on 2026-10-22
