import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Lebesgue_outer_measure


/--
[Lebesgue_outer_measure.union_of_separated](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E F : Set (EuclideanSpace' d)}
-- given
  (hd: 0 < d)
  (hsep: set_dist E F > 0) :
-- imply
  Lebesgue_outer_measure (E ∪ F) = Lebesgue_outer_measure E + Lebesgue_outer_measure F :=
-- proof
  Lebesgue_outer_measure.union_of_separated hd hsep


-- created on 2026-10-22
