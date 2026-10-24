import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open Lebesgue_outer_measure


/--
[le_of_nat_cover](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
  {S : ℕ → Box d}
-- given
  (hd: 0 < d)
  (hcover : E ⊆ ⋃ n, (S n).toSet) :
-- imply
  Lebesgue_outer_measure E ≤ ∑' n, (S n).volume.toEReal :=
-- proof
  Lebesgue_outer_measure.le_of_nat_cover hd E S hcover


-- created on 2026-10-22
