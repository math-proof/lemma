import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_9_10
open Chapter9


/--
[unbounded_iff'](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_10.lean)
-/
@[path]
private lemma main
  {X:Set ℝ} :
-- imply
  ¬ BddAbove X ↔ sSup ((fun x:ℝ ↦ (x:EReal)) '' X) = ⊤ :=
-- proof
  Chapter9.BddAbove.unbounded_iff' X


-- created on 2026-10-20
