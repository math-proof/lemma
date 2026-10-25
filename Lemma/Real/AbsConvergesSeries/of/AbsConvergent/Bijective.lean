import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_8_2.Part4
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8
open Chapter8.AbsConvergent


/--
[AbsConvergent.comp](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  {f:X → ℝ}
  {g:ℕ → X}
-- given
  (h: Bijective g)
  (hf: AbsConvergent f) :
-- imply
  (f ∘ g:Series).absConverges :=
-- proof
  Chapter8.AbsConvergent.comp h hf


-- created on 2026-10-22
