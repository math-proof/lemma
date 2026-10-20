import Mathlib
import sympy.Basic
import sympy.analysis.Section_9_10
open Chapter9


/--
[unbounded_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_10.lean)
-/
@[path]
private lemma main
  {X:Set ℝ} :
-- imply
  ¬ BddBelow X ↔ ∀ M, ∃ x ∈ X, x < M :=
-- proof
  Chapter9.BddBelow.unbounded_iff X


-- created on 2026-10-20
