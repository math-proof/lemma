import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open AlmostAlways


/--
[AlmostAlways.ofAlways](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {P: EuclideanSpace' d → Prop}
-- given
  (h: ∀ x, P x) :
-- imply
  AlmostAlways P :=
-- proof
  AlmostAlways.ofAlways h


-- created on 2026-10-22
