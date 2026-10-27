import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
open scoped Pointwise
open Lebesgue_measure


/--
[Lebesgue_measure.Icc_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_3.lean)
-/
@[path]
private lemma main
  {a b : ℝ}
-- given
  (hab : a ≤ b) :
-- imply
  Lebesgue_measure (Real.equiv_EuclideanSpace' '' Set.Icc a b) = (b - a : ℝ) :=
-- proof
  Lebesgue_measure.Icc_eq a b hab


-- created on 2026-10-22
