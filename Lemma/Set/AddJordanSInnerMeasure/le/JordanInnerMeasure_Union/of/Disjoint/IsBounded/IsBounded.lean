import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_2


/--
[Jordan_inner_add_le](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E F: Set (EuclideanSpace' d)}
-- given
  (hE: Bornology.IsBounded E)
  (hF: Bornology.IsBounded F)
  (hdisj: Disjoint E F) :
-- imply
  Jordan_inner_measure E + Jordan_inner_measure F ≤ Jordan_inner_measure (E ∪ F) :=
-- proof
  Jordan_inner_add_le hE hF hdisj


-- created on 2026-10-22
