import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_2
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8
open Chapter8.Sum'


/--
[Sum'.eq_tsum](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  {f:X → ℝ}
-- given
  (h: AbsConvergent' f) :
-- imply
  Sum' f = ∑' x, f x :=
-- proof
  Chapter8.Sum'.eq_tsum f h


-- created on 2026-10-22
