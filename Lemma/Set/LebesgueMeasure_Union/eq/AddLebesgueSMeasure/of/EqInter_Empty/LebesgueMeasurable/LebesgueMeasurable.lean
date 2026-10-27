import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_2_2.Part3
open BoundedInterval
open Lebesgue_measure


/--
[Lebesgue_measure.union](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E F: Set (EuclideanSpace' d)}
-- given
  (hE: LebesgueMeasurable E)
  (hF: LebesgueMeasurable F)
  (hdisj: E ∩ F = ∅) :
-- imply
  Lebesgue_measure (E ∪ F) = Lebesgue_measure E + Lebesgue_measure F :=
-- proof
  Lebesgue_measure.union hE hF hdisj


-- created on 2026-10-22
