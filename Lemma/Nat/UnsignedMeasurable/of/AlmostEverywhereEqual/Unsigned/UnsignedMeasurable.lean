import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_2
open UnsignedMeasurable


/--
[UnsignedMeasurable.aeEqual](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f g: EuclideanSpace' d → EReal}
-- given
  (hf: UnsignedMeasurable f)
  (hg : Unsigned g)
  (heq: AlmostEverywhereEqual f g) :
-- imply
  UnsignedMeasurable g :=
-- proof
  UnsignedMeasurable.aeEqual hf hg heq


-- created on 2026-10-22
