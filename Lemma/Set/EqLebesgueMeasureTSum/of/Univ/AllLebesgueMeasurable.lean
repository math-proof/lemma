import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_2
open BoundedInterval
open Lebesgue_measure


/--
[Lebesgue_measure.finite_union](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_2.lean)
-/
@[path]
private lemma main
  {d n:ℕ}
  {E: Fin n → Set (EuclideanSpace' d)}
-- given
  (hmes: ∀ n, LebesgueMeasurable (E n))
  (hdisj: Set.univ.PairwiseDisjoint E) :
-- imply
  Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) :=
-- proof
  Lebesgue_measure.finite_union hmes hdisj


-- created on 2026-10-22
