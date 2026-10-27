import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Lebesgue_outer_measure


/--
[Lebesgue_outer_measure.of_empty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ} :
-- imply
  Lebesgue_outer_measure (∅: Set (EuclideanSpace' d)) = 0 :=
-- proof
  Lebesgue_outer_measure.of_empty d


-- created on 2026-10-22
