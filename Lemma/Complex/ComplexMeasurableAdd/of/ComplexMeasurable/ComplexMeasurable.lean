import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_2
open ComplexMeasurable


/--
[ComplexMeasurable.add](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f g: EuclideanSpace' d → ℂ}
-- given
  (hf: ComplexMeasurable f)
  (hg: ComplexMeasurable g) :
-- imply
  ComplexMeasurable (f + g) :=
-- proof
  ComplexMeasurable.add hf hg


-- created on 2026-10-22
