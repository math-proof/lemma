import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_7_3
open Real
open Chapter7
open Chapter7.Series


/--
[Series.partial_le_sum_of_nonneg](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_3.lean)
-/
@[path]
private lemma main
  {s: Series}
  {N : ℤ}
-- given
  (hnon: s.nonneg)
  (hconv: s.converges) :
-- imply
  s.partial N ≤ s.sum :=
-- proof
  Chapter7.Series.partial_le_sum_of_nonneg hnon hconv N


-- created on 2026-10-22
