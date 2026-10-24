import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_1
open Chapter11.BoundedInterval
open Chapter11


/--
[BoundedInterval.empty_of_lt](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
-- given
  (h: I.b < I.a) :
-- imply
  (I:Set ℝ) = ∅ :=
-- proof
  Chapter11.BoundedInterval.empty_of_lt h


-- created on 2026-10-22
