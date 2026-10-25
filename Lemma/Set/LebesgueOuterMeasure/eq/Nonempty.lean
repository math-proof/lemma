import Mathlib
import sympy.Basic
import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
open BoundedInterval
open Classical


/--
[Lebesgue_outer_measure_of_dim_zero](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_0.lean)
-/
@[path]
private lemma main
  {E: Set (EuclideanSpace' 0)} :
-- imply
  Lebesgue_outer_measure E = if E.Nonempty then 1 else 0 :=
-- proof
  Lebesgue_outer_measure_of_dim_zero


-- created on 2026-10-22
