import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_7_3
open Real
open Chapter7
open Chapter7.Series


/--
[Series.converges_of_nonneg_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_3.lean)
-/
@[path]
private lemma main
  {s: Series}
-- given
  (h: s.nonneg) :
-- imply
  s.converges ↔ ∃ M, ∀ N, s.partial N ≤ M :=
-- proof
  Chapter7.Series.converges_of_nonneg_iff h


-- created on 2026-10-22
