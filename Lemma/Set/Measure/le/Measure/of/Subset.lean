import Mathlib
import sympy.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
open JordanMeasurable


/--
[JordanMeasurable.mono](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E F : Set (EuclideanSpace' d)}
-- given
  (hE: JordanMeasurable E)
  (hF: JordanMeasurable F)
  (hEF: E ⊆ F) :
-- imply
  hE.measure ≤ hF.measure :=
-- proof
  JordanMeasurable.mono hE hF hEF


-- created on 2026-10-22
