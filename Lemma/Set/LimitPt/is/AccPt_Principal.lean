import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_9_1.Part3
open Chapter9
open Chapter9.LimitPt


/--
[LimitPt.iff_AccPt](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_1.lean)
-/
@[path]
private lemma main
  {x:ℝ}
  {X: Set ℝ} :
-- imply
  LimitPt x X ↔ AccPt x (.principal X) :=
-- proof
  Chapter9.LimitPt.iff_AccPt x X


-- created on 2026-10-22
