import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_2


/--
[Jordan_inner_le_outer](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: Bornology.IsBounded E) :
-- imply
  Jordan_inner_measure E ≤ Jordan_outer_measure E :=
-- proof
  Jordan_inner_le_outer hE


-- created on 2026-10-22
