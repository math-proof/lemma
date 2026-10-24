import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_2
open JordanMeasurable


/--
[JordanMeasurable.mes_of_disjUnion](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E F : Set (EuclideanSpace' d)}
-- given
  (hE: JordanMeasurable E)
  (hF: JordanMeasurable F)
  (hEF: Disjoint E F) :
-- imply
  (hE.union hF).measure = hE.measure + hF.measure :=
-- proof
  JordanMeasurable.mes_of_disjUnion hE hF hEF


-- created on 2026-10-22
