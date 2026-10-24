import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_2
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8
open Chapter8.AbsConvergent


/--
[AbsConvergent.mk](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  {X: Type}
  {f:X → ℝ}
  {g:ℕ → X}
-- given
  (h: Bijective g)
  (hfg: (f ∘ g:Series).absConverges) :
-- imply
  AbsConvergent f :=
-- proof
  Chapter8.AbsConvergent.mk h hfg


-- created on 2026-10-22
