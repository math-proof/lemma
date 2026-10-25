import Mathlib
import sympy.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
open JordanMeasurable


/--
[JordanMeasurable.symmDiff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E F : Set (EuclideanSpace' d)}
-- given
  (hE: JordanMeasurable E)
  (hF: JordanMeasurable F) :
-- imply
  JordanMeasurable (symmDiff E F) :=
-- proof
  JordanMeasurable.symmDiff hE hF


-- created on 2026-10-22
