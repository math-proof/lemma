import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
open PreL1


/--
[PreL1.dist_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {F G: PreL1 d} :
-- imply
  dist F G = ‖F-G‖ :=
-- proof
  PreL1.dist_eq F G


-- created on 2026-10-22
