import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_2
open JordanMeasurable


/--
[JordanMeasurable.sdiff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E F : Set (EuclideanSpace' d)}
-- given
  (hE: JordanMeasurable E)
  (hF: JordanMeasurable F) :
-- imply
  JordanMeasurable (E \ F) :=
-- proof
  JordanMeasurable.sdiff hE hF


-- created on 2026-10-22
