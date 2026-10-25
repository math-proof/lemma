import Mathlib
import sympy.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4


/--
[Jordan_outer_subadd](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E F: Set (EuclideanSpace' d)}
-- given
  (hE: Bornology.IsBounded E)
  (hF: Bornology.IsBounded F) :
-- imply
  Jordan_outer_measure (E ∪ F) ≤ Jordan_outer_measure E + Jordan_outer_measure F :=
-- proof
  Jordan_outer_subadd hE hF


-- created on 2026-10-22
