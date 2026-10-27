import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Lebesgue_outer_measure


/--
[Lebesgue_outer_measure.elementary_dim_zero](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {E: Set (EuclideanSpace' 0)}
-- given
  (hE: IsElementary E) :
-- imply
  Lebesgue_outer_measure E = hE.measure :=
-- proof
  Lebesgue_outer_measure.elementary_dim_zero E hE


-- created on 2026-10-22
