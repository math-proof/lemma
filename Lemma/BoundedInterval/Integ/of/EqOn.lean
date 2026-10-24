import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_3
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[integ_congr](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_3.lean)
-/
@[path]
private lemma main
  {f g:ℝ → ℝ}
  {I: BoundedInterval}
-- given
  (h: Set.EqOn f g I) :
-- imply
  integ f I = integ g I :=
-- proof
  Chapter11.integ_congr h


-- created on 2026-10-22
