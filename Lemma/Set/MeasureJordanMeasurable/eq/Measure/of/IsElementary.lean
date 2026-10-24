import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_2
open JordanMeasurable


/--
[JordanMeasurable.mes_of_elementary](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: IsElementary E) :
-- imply
  hE.jordanMeasurable.measure = hE.measure :=
-- proof
  JordanMeasurable.mes_of_elementary hE


-- created on 2026-10-22
