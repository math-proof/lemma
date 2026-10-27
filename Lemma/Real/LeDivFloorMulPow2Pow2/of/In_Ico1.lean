import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open Remark_1_3_10


/--
[binaryDigit_partial_sum_le](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {x : ℝ}
  {n : ℕ}
-- given
  (hx : x ∈ Set.Ico (0:ℝ) 1) :
-- imply
  (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n ≤ x :=
-- proof
  Remark_1_3_10.binaryDigit_partial_sum_le hx n


-- created on 2026-10-22
