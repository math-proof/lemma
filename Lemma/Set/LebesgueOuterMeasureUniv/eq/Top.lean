import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open Lebesgue_outer_measure


/--
[Lebesgue_outer_measure.univ](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {hd: 0 < d} :
-- imply
  Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d)) = ⊤ :=
-- proof
  Lebesgue_outer_measure.univ (hd := hd)


-- created on 2026-10-22
