import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open Remark_1_3_10


/--
[binaryDigit_zero_implies_upper_bound](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {y : ℝ}
  {k : ℕ}
-- given
  (hy : y ∈ Set.Ico (0:ℝ) 1)
  (hbk : binaryDigit y (k + 1) = 0) :
-- imply
  y < (⌊(2:ℝ)^k * y⌋₊ : ℝ) / (2:ℝ)^k + (1:ℝ) / (2:ℝ)^(k + 1) :=
-- proof
  Remark_1_3_10.binaryDigit_zero_implies_upper_bound hy k hbk


-- created on 2026-10-22
