import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open AlmostEverywhereEqual


/--
[AlmostEverywhereEqual.trans](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f g h: EuclideanSpace' d → X}
-- given
  (hfg: AlmostEverywhereEqual f g)
  (hgh: AlmostEverywhereEqual g h) :
-- imply
  AlmostEverywhereEqual f h :=
-- proof
  AlmostEverywhereEqual.trans hfg hgh


-- created on 2026-10-22
