import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open AlmostEverywhereEqual


/--
[AlmostEverywhereEqual.equivalence](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ} :
-- imply
  Equivalence (@AlmostEverywhereEqual d X) :=
-- proof
  AlmostEverywhereEqual.equivalence


-- created on 2026-10-22
