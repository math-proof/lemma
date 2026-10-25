import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open Remark_1_3_10


/--
[binaryDigit_partial_sum_lt](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {x : ℝ}
  {n : ℕ} :
-- imply
  x < (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n + (1:ℝ) / (2:ℝ)^n :=
-- proof
  Remark_1_3_10.binaryDigit_partial_sum_lt x n


-- created on 2026-10-22
