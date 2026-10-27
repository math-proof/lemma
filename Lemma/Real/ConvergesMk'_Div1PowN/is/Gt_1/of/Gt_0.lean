import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_7_3
open Real
open Chapter7
open Chapter7.Series


/--
[Series.converges_qseries](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_3.lean)
-/
@[path]
private lemma main
  {q: ℝ}
-- given
  (hq: q > 0) :
-- imply
  (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ q : Series).converges ↔ (q>1) :=
-- proof
  Chapter7.Series.converges_qseries q hq


-- created on 2026-10-22
