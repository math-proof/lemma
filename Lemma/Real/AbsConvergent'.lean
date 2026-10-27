import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_8_2.Part4
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8
open Chapter8.AbsConvergent'


/--
[AbsConvergent'.of_finite](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  {X:Type} [Finite X]
  {f:X → ℝ} :
-- imply
  AbsConvergent' f :=
-- proof
  Chapter8.AbsConvergent'.of_finite f


-- created on 2026-10-22
