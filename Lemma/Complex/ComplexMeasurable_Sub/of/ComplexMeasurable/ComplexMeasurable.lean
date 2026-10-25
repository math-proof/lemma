import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open ComplexMeasurable


/--
[ComplexMeasurable.sub](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f g: EuclideanSpace' d → ℂ}
-- given
  (hf: ComplexMeasurable f)
  (hg: ComplexMeasurable g) :
-- imply
  ComplexMeasurable (f - g) :=
-- proof
  ComplexMeasurable.sub hf hg


-- created on 2026-10-22
