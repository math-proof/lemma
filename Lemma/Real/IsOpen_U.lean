import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Remark_1_2_8


/--
[U_isOpen](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {ε : ℝ} :
-- imply
  IsOpen (U ε) :=
-- proof
  Remark_1_2_8.U_isOpen ε


-- created on 2026-10-22
