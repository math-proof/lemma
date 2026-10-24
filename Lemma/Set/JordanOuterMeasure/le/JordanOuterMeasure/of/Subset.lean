import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval


/--
[Jordan_outer_measure_mono](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {E F : Set (EuclideanSpace' 1)}
  {hF: Bornology.IsBounded F}
-- given
  (hEF: E ⊆ F) :
-- imply
  Jordan_outer_measure E ≤ Jordan_outer_measure F :=
-- proof
  Jordan_outer_measure_mono hEF hF


-- created on 2026-10-22
