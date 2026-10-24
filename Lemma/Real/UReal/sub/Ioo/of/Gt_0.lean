import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open Remark_1_2_8


/--
[U_real_subset](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {ε : ℝ}
-- given
  (hε : 0 < ε) :
-- imply
  U_real ε ⊆ Set.Ioo (-ε) (1 + ε) :=
-- proof
  Remark_1_2_8.U_real_subset ε hε


-- created on 2026-10-22
