import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_7_3
open Real
open Chapter7
open Chapter7.Series


/--
[Series.cauchy_criterion](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_3.lean)
-/
@[path]
private lemma main
  {s:Series}
-- given
  (hm: s.m = 1)
  (hs:s.nonneg)
  (hmono: ∀ n ≥ 1, s.seq (n+1) ≤ s.seq n) :
-- imply
  s.converges ↔ (fun k ↦ 2^k * s.seq (2^k): Series).converges :=
-- proof
  Chapter7.Series.cauchy_criterion hm hs hmono


-- created on 2026-10-22
