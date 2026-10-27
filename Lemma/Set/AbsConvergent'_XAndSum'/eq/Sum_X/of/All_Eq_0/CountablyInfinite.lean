import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_8_2.Part4
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8
open Chapter8.Sum'


/--
[Sum'.of_countable_supp](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  {f:X → ℝ}
  {A: Set X}
-- given
  (hA: CountablyInfinite A)
  (hfA : ∀ x ∉ A, f x = 0)
  (hconv: AbsConvergent' f) :
-- imply
  AbsConvergent' (fun x:A ↦ f x) ∧ Sum' f = Sum (fun x:A ↦ f x) :=
-- proof
  Chapter8.Sum'.of_countable_supp hA hfA hconv


-- created on 2026-10-22
