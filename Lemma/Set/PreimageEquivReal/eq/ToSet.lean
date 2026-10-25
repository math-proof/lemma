import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Remark_1_2_8


/--
[unit_interval_eq_box](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  :
-- imply
  EuclideanSpace'.equiv_Real ⁻¹' Set.Icc 0 1 = unit_box_1D.toSet :=
-- proof
  Remark_1_2_8.unit_interval_eq_box


-- created on 2026-10-22
