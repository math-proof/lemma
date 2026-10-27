import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_9_10
open Chapter9


/--
[unbounded_iff'](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_10.lean)
-/
@[path]
private lemma main
  {X:Set ℝ} :
-- imply
  ¬ BddBelow X ↔ sInf ((fun x:ℝ ↦ (x:EReal)) '' X) = ⊥ :=
-- proof
  Chapter9.BddBelow.unbounded_iff' X


-- created on 2026-10-20
