import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_7_3
open Real
open Chapter7
open Chapter7.Series


/--
[Series.sum_of_nonneg_lt](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_3.lean)
-/
@[path]
private lemma main
  {s: Series}
  {M:ℝ}
-- given
  (h: s.nonneg)
  (hM: ∀ N, s.partial N ≤ M) :
-- imply
  s.sum ≤ M :=
-- proof
  Chapter7.Series.sum_of_nonneg_lt h hM


-- created on 2026-10-22
