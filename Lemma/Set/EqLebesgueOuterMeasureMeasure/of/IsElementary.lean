import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Lebesgue_outer_measure


/--
[Lebesgue_outer_measure.elementary](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: IsElementary E) :
-- imply
  Lebesgue_outer_measure E = hE.measure :=
-- proof
  Lebesgue_outer_measure.elementary E hE


-- created on 2026-10-22
