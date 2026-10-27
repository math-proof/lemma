import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_8_2.Part4
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8


/--
[sum_comm](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  {f:ℕ × ℕ → ℝ}
-- given
  (hf:AbsConvergent f) :
-- imply
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).sum = (fun m ↦ ((fun n ↦ f (n, m)):Series).sum:Series).sum :=
-- proof
  Chapter8.sum_comm hf


-- created on 2026-10-22
