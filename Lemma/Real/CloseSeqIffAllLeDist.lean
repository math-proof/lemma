import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Real
open Real.CloseSeq


/--
[Real.CloseSeq.coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {ε : ℝ}
  {a : ℕ → ℝ}
  {L : ℝ} :
-- imply
  (ε.CloseSeq a L) ↔ ∀ n, dist (a n) L ≤ ε :=
-- proof
  Real.CloseSeq.coe ε a L


-- created on 2026-10-22
