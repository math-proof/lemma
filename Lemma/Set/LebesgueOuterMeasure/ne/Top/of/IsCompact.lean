import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Lebesgue_outer_measure


/--
[Lebesgue_outer_measure.finite_of_compact](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {E : Set (EuclideanSpace' d)}
-- given
  (hE : IsCompact E) :
-- imply
  Lebesgue_outer_measure E ≠ ⊤ :=
-- proof
  Lebesgue_outer_measure.finite_of_compact hE


-- created on 2026-10-22
