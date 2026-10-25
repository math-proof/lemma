import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Remark_1_2_8


/--
[U_lebesgue_le](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {ε : ℝ}
-- given
  (hε : 0 < ε) :
-- imply
  Lebesgue_outer_measure (U ε) ≤ ((2 * ε : ℝ) : EReal) :=
-- proof
  Remark_1_2_8.U_lebesgue_le ε hε


-- created on 2026-10-22
