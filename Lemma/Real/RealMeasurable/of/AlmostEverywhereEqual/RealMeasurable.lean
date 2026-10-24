import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_2
open RealMeasurable


/--
[RealMeasurable.aeEqual](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f g: EuclideanSpace' d → ℝ}
-- given
  (hf: RealMeasurable f)
  (heq: AlmostEverywhereEqual f g) :
-- imply
  RealMeasurable g :=
-- proof
  RealMeasurable.aeEqual hf heq


-- created on 2026-10-22
