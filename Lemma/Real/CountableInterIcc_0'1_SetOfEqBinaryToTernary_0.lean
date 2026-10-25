import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open Remark_1_3_10


/--
[f_zero_set_in_interval_countable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  :
-- imply
  (Set.Icc (0:ℝ) 1 ∩ {x | binaryToTernary x = 0}).Countable :=
-- proof
  Remark_1_3_10.f_zero_set_in_interval_countable


-- created on 2026-10-22
