import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_8_2.Part4
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8
open Chapter8.Sum


/--
[Sum.eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  {f:X → ℝ}
  {g:ℕ → X}
-- given
  (h: Bijective g)
  (hfg: (f ∘ g:Series).absConverges) :
-- imply
  (f ∘ g:Series).convergesTo (Sum f) :=
-- proof
  Chapter8.Sum.eq h hfg


-- created on 2026-10-22
