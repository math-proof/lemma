import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_2
open Remark_1_3_10


/--
[binaryDigit_one_implies_lower_bound](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {x : ℝ}
  {k : ℕ}
-- given
  (hx : x ∈ Set.Ico (0:ℝ) 1)
  (hbk : binaryDigit x (k + 1) = 1) :
-- imply
  (⌊(2:ℝ)^k * x⌋₊ : ℝ) / (2:ℝ)^k + (1:ℝ) / (2:ℝ)^(k + 1) ≤ x :=
-- proof
  Remark_1_3_10.binaryDigit_one_implies_lower_bound hx k hbk


-- created on 2026-10-22
