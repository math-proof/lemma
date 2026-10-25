import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open AlmostEverywhereEqual


/--
[AlmostEverywhereEqual.symm](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f g: EuclideanSpace' d → X}
-- given
  (h: AlmostEverywhereEqual f g) :
-- imply
  AlmostEverywhereEqual g f :=
-- proof
  AlmostEverywhereEqual.symm h


-- created on 2026-10-22
