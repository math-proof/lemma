import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Lebesgue_outer_measure


/--
[Lebesgue_outer_measure.exists_open_superset_measure_le](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
  {ε : EReal}
-- given
  (hε : 0 < ε) :
-- imply
  ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure U ≤ Lebesgue_outer_measure E + ε :=
-- proof
  Lebesgue_outer_measure.exists_open_superset_measure_le E ε hε


-- created on 2026-10-22
