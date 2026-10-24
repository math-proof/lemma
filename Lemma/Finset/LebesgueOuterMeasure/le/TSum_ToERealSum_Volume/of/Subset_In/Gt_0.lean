import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open Lebesgue_outer_measure


/--
[le_of_finset_cover](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
  {I : ℕ → Finset (Box d)}
-- given
  (hd: 0 < d)
  (hcover : E ⊆ ⋃ n, ⋃ B ∈ I n, B.toSet) :
-- imply
  Lebesgue_outer_measure E ≤ ∑' n, (∑ B ∈ I n, B.volume).toEReal :=
-- proof
  Lebesgue_outer_measure.le_of_finset_cover hd E I hcover


-- created on 2026-10-22
