import Mathlib
import sympy.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_2_2.Part3
open BoundedInterval
open Lebesgue_measure


/--
[Lebesgue_measure.countable_union](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: ℕ → Set (EuclideanSpace' d)}
-- given
  (hmes: ∀ n, LebesgueMeasurable (E n))
  (hdisj: Set.univ.PairwiseDisjoint E) :
-- imply
  Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) :=
-- proof
  Lebesgue_measure.countable_union hmes hdisj


-- created on 2026-10-22
