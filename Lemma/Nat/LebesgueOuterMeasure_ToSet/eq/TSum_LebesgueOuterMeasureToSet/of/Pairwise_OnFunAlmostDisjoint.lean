import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Lebesgue_outer_measure


/--
[Lebesgue_outer_measure.union_of_almost_disjoint](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B : ℕ → Box d}
-- given
  (h : Pairwise (Function.onFun AlmostDisjoint B)) :
-- imply
  Lebesgue_outer_measure (⋃ i, (B i).toSet) = ∑' i, Lebesgue_outer_measure (B i).toSet :=
-- proof
  Lebesgue_outer_measure.union_of_almost_disjoint h


-- created on 2026-10-22
