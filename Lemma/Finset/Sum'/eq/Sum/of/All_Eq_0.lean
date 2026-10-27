import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_8_2.Part4
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8
open Chapter8.Sum'


/--
[Sum'.of_finsupp](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  {X:Type}
  {f:X → ℝ}
  {A: Finset X}
-- given
  (h: ∀ x ∉ A, f x = 0) :
-- imply
  Sum' f = ∑ x ∈ A, f x :=
-- proof
  Chapter8.Sum'.of_finsupp h


-- created on 2026-10-22
