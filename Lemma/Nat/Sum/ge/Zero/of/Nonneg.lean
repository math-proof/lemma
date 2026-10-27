import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_7_3
open Real
open Chapter7
open Chapter7.Series


/--
[Series.sum_of_nonneg](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_3.lean)
-/
@[path]
private lemma main
  {s:Series}
-- given
  (hnon: s.nonneg) :
-- imply
  0 ≤ s.sum :=
-- proof
  Chapter7.Series.sum_of_nonneg hnon


-- created on 2026-10-22
