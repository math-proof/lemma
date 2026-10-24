import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_1
open Real


/--
[Real.closeSeq_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {ε: ℝ}
  {a: Chapter6.Sequence}
  {L:ℝ} :
-- imply
  ε.CloseSeq a L ↔ ∀ n ≥ a.m, dist (a n) L ≤ ε :=
-- proof
  Real.closeSeq_def ε a L


-- created on 2026-10-22
