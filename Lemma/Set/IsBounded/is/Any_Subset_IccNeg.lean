import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_9_1.Part3
open Chapter9


/--
[isBounded_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_1.lean)
-/
@[path]
private lemma main
  {X: Set ℝ} :
-- imply
  Bornology.IsBounded X ↔ ∃ M > 0, X ⊆ .Icc (-M) M :=
-- proof
  Chapter9.isBounded_def X


-- created on 2026-10-22
