import Mathlib
import sympy.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
open JordanMeasurable


/--
[JordanMeasurable.eq_outer](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: JordanMeasurable E) :
-- imply
  hE.measure = Jordan_outer_measure E :=
-- proof
  JordanMeasurable.eq_outer hE


-- created on 2026-10-22
