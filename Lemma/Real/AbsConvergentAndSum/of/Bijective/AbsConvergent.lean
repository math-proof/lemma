import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_8_2.Part4
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8
open Chapter8.Sum


/--
[Sum.of_comp](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  {X Y:Type}
  {f:X → ℝ}
  {g: Y → X}
-- given
  (h: AbsConvergent f)
  (hbij: Bijective g) :
-- imply
  AbsConvergent (f ∘ g) ∧ Sum f = Sum (f ∘ g) :=
-- proof
  Chapter8.Sum.of_comp h hbij


-- created on 2026-10-22
