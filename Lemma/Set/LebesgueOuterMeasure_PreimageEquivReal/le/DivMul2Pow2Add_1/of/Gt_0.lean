import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open Remark_1_2_8


/--
[component_lebesgue_le](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {ε : ℝ}
  {n : ℕ}
-- given
  (hε : 0 < ε) :
-- imply
  Lebesgue_outer_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (q n - ε / 2^(n+1)) (q n + ε / 2^(n+1)))
    ≤ ((2 * ε / 2^(n+1) : ℝ) : EReal) :=
-- proof
  Remark_1_2_8.component_lebesgue_le ε hε n


-- created on 2026-10-22
