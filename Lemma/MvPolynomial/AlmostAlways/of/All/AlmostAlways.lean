import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open AlmostAlways


/--
[AlmostAlways.mp](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {P Q: EuclideanSpace' d → Prop}
-- given
  (hP: AlmostAlways P)
  (himp: ∀ x, P x → Q x) :
-- imply
  AlmostAlways Q :=
-- proof
  AlmostAlways.mp hP himp


-- created on 2026-10-22
