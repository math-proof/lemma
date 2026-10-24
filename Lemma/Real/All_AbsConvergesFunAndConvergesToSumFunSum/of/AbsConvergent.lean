import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_2
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8


/--
[sum_of_sum_of_AbsConvergent'](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  {f:ℕ × ℕ → ℝ}
-- given
  (hf:AbsConvergent f) :
-- imply
  (∀ m, ((fun n ↦ f (n, m)):Series).absConverges) ∧
    (fun m ↦ ((fun n ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) :=
-- proof
  Chapter8.sum_of_sum_of_AbsConvergent' hf


-- created on 2026-10-22
