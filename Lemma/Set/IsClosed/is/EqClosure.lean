import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_9_1.Part3
open Chapter9


/--
[isClosed_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_1.lean)
-/
@[path]
private lemma main
  {X:Set ℝ} :
-- imply
  IsClosed X ↔ closure X = X :=
-- proof
  Chapter9.isClosed_def X


-- created on 2026-10-22
