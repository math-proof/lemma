import Mathlib
import sympy.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4


/--
[Jordan_inner_measure_nonneg](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)} :
-- imply
  0 ≤ Jordan_inner_measure E :=
-- proof
  Jordan_inner_measure_nonneg E


-- created on 2026-10-22
