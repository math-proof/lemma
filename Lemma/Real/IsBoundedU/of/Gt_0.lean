import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Remark_1_2_8


/--
[U_isBounded](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {ε : ℝ}
-- given
  (hε : 0 < ε) :
-- imply
  Bornology.IsBounded (U ε) :=
-- proof
  Remark_1_2_8.U_isBounded ε hε


-- created on 2026-10-22
