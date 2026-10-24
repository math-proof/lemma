import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_2


/--
[Jordan_outer_measure_nonneg](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)} :
-- imply
  0 ≤ Jordan_outer_measure E :=
-- proof
  Jordan_outer_measure_nonneg E


-- created on 2026-10-22
