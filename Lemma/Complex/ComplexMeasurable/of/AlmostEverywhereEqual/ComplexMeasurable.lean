import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open ComplexMeasurable


/--
[ComplexMeasurable.aeEqual](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f g: EuclideanSpace' d → ℂ}
-- given
  (hf: ComplexMeasurable f)
  (heq: AlmostEverywhereEqual f g) :
-- imply
  ComplexMeasurable g :=
-- proof
  ComplexMeasurable.aeEqual hf heq


-- created on 2026-10-22
