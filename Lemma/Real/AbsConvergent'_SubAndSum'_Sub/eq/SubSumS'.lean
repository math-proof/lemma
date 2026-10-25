import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_8_2.Part4
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8
open Chapter8.Sum'


/--
[Sum'.sub](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  {f g:X → ℝ}
-- given
  (hf: AbsConvergent' f)
  (hg: AbsConvergent' g) :
-- imply
  AbsConvergent' (f-g) ∧ Sum' (f - g) = Sum' f - Sum' g :=
-- proof
  Chapter8.Sum'.sub hf hg


-- created on 2026-10-22
