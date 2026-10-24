import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open Lebesgue_outer_measure


/--
[of_Icc](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {a b : ℝ}
-- given
  (hab : a ≤ b) :
-- imply
  Lebesgue_outer_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Icc a b) = ((b - a : ℝ) : EReal) :=
-- proof
  Lebesgue_outer_measure.of_Icc a b hab


-- created on 2026-10-22
