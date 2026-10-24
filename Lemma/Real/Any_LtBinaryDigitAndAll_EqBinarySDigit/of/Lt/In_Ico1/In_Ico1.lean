import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_2
open Remark_1_3_10


/--
[binaryDigit_first_diff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {x y : ℝ}
-- given
  (hx : x ∈ Set.Ico (0:ℝ) 1)
  (hy : y ∈ Set.Ico (0:ℝ) 1)
  (hxy : x < y) :
-- imply
  ∃ k, binaryDigit x (k + 1) < binaryDigit y (k + 1) ∧
    ∀ j < k, binaryDigit x (j + 1) = binaryDigit y (j + 1) :=
-- proof
  Remark_1_3_10.binaryDigit_first_diff hx hy hxy


-- created on 2026-10-22
