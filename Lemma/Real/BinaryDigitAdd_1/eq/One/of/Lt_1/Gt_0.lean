import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open Remark_1_3_10


/--
[binaryDigit_exists_one_of_pos](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {x : ℝ}
-- given
  (hx_pos : 0 < x)
  (hx_lt : x < 1) :
-- imply
  ∃ j, binaryDigit x (j + 1) = 1 :=
-- proof
  Remark_1_3_10.binaryDigit_exists_one_of_pos hx_pos hx_lt


-- created on 2026-10-22
