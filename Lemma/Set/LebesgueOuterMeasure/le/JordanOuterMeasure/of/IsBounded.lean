import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
open BoundedInterval


/--
[Lebesgue_outer_measure_le_Jordan](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_0.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: Bornology.IsBounded E) :
-- imply
  Lebesgue_outer_measure E ≤ Jordan_outer_measure E :=
-- proof
  Lebesgue_outer_measure_le_Jordan hE


-- created on 2026-10-22
