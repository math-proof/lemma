import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_8_2.Part4
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8
open Chapter8.AbsConvergent'


/--
[AbsConvergent'.subtype](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  {X:Type}
  {f:X → ℝ}
  {A: Set X}
-- given
  (hf: AbsConvergent' f) :
-- imply
  AbsConvergent' (fun x:A ↦ f x) :=
-- proof
  Chapter8.AbsConvergent'.subtype hf A


-- created on 2026-10-22
