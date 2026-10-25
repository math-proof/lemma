import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Lebesgue_outer_measure


/--
[exists_cover_close](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
  {ε: ℝ}
-- given
  (hd: 0 < d)
  (hε: 0 < ε)
  (h_finite: Lebesgue_outer_measure E ≠ ⊤) :
-- imply
  ∃ (S: ℕ → Box d), E ⊆ ⋃ n, (S n).toSet ∧
        ∑' n, (S n).volume.toEReal ≤ Lebesgue_outer_measure E + ε :=
-- proof
  Lebesgue_outer_measure.exists_cover_close hd E ε hε h_finite


-- created on 2026-10-22
