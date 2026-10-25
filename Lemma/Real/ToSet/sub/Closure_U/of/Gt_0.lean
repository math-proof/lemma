import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Remark_1_2_8


/--
[U_closure_contains_unit_box](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {ε : ℝ}
-- given
  (hε : 0 < ε) :
-- imply
  unit_box_1D.toSet ⊆ closure (U ε) :=
-- proof
  Remark_1_2_8.U_closure_contains_unit_box ε hε


-- created on 2026-10-22
