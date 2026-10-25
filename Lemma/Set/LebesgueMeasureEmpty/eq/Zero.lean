import Mathlib
import sympy.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_2_2.Part3
open BoundedInterval
open Lebesgue_measure


/--
[Lebesgue_measure.empty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_2.lean)
-/
@[path]
private lemma main
  {d:ℕ} :
-- imply
  Lebesgue_measure (∅: Set (EuclideanSpace' d)) = 0 :=
-- proof
  Lebesgue_measure.empty


-- created on 2026-10-22
