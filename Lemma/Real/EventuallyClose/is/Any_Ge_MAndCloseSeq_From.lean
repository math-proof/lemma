import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Real


/--
[Real.eventuallyClose_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {ε: ℝ}
  {a: Chapter6.Sequence}
  {L:ℝ} :
-- imply
  ε.EventuallyClose a L ↔ ∃ N, (N ≥ a.m) ∧ ε.CloseSeq (a.from N) L :=
-- proof
  Real.eventuallyClose_def ε a L


-- created on 2026-10-22
