import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Lebesgue_outer_measure


/--
[of_Ioo_le](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : a < b) :
-- imply
  Lebesgue_outer_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo a b) ≤ ((b - a : ℝ) : EReal) :=
-- proof
  Lebesgue_outer_measure.of_Ioo_le a b h


-- created on 2026-10-22
