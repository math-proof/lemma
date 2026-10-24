import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open Box


/--
[not_intersects_both_of_diameter_lt](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
  {E F : Set (EuclideanSpace' d)}
-- given
  (h : B.diameter < set_dist E F) :
-- imply
  ¬((B.toSet ∩ E).Nonempty ∧ (B.toSet ∩ F).Nonempty) :=
-- proof
  Box.not_intersects_both_of_diameter_lt B E F h


-- created on 2026-10-22
