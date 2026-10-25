import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_8_2.Part4
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8
open Chapter8.AbsConvergent'


/--
[AbsConvergent'.of_countable](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  {f:X → ℝ}
-- given
  (hX:CountablyInfinite X) :
-- imply
  AbsConvergent' f ↔ AbsConvergent f :=
-- proof
  Chapter8.AbsConvergent'.of_countable hX


-- created on 2026-10-22
