import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_2
open LebesgueMeasurable


/--
[LebesgueMeasurable.empty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_2.lean)
-/
@[path]
private lemma main
  {d:ℕ} :
-- imply
  LebesgueMeasurable (∅: Set (EuclideanSpace' d)) :=
-- proof
  LebesgueMeasurable.empty


-- created on 2026-10-22
