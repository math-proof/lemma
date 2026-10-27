import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Remark_1_2_8


/--
[Jordan_outer_unit_box](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  :
-- imply
  Jordan_outer_measure unit_box_1D.toSet = 1 :=
-- proof
  Remark_1_2_8.Jordan_outer_unit_box


-- created on 2026-10-22
