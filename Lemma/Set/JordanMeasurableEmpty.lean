import Mathlib
import sympy.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
open JordanMeasurable


/--
[JordanMeasurable.empty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ} :
-- imply
  JordanMeasurable (∅: Set (EuclideanSpace' d)) :=
-- proof
  JordanMeasurable.empty d


-- created on 2026-10-22
