import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_9_1.Part3
open Chapter9


/--
[closure_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_1.lean)
-/
@[path]
private lemma main
  {X:Set ℝ} :
-- imply
  closure X = { x | AdherentPt x X } :=
-- proof
  Chapter9.closure_def X


-- created on 2026-10-22
