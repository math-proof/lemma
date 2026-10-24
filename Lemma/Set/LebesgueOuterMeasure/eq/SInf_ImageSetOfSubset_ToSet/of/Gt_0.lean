import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_0
open BoundedInterval


/--
[Lebesgue_outer_measure_eq_nat_indexed](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_0.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hd: 0 < d) :
-- imply
  Lebesgue_outer_measure E =
      sInf (((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet }) :=
-- proof
  Lebesgue_outer_measure_eq_nat_indexed hd E


-- created on 2026-10-22
