import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open Remark_1_2_8


/--
[U_real_closure_contains_unit_interval](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {ε : ℝ}
-- given
  (hε : 0 < ε) :
-- imply
  Set.Icc 0 1 ⊆ closure (U_real ε) :=
-- proof
  Remark_1_2_8.U_real_closure_contains_unit_interval ε hε


-- created on 2026-10-22
