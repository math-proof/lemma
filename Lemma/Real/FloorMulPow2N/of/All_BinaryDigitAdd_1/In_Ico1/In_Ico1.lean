import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open Remark_1_3_10


/--
[floor_eq_of_binaryDigit_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {x y : ℝ}
-- given
  (hx : x ∈ Set.Ico (0:ℝ) 1)
  (hy : y ∈ Set.Ico (0:ℝ) 1)
  (heq : ∀ j < n, binaryDigit x (j + 1) = binaryDigit y (j + 1)) :
-- imply
  ⌊(2:ℝ)^n * x⌋₊ = ⌊(2:ℝ)^n * y⌋₊ :=
-- proof
  Remark_1_3_10.floor_eq_of_binaryDigit_eq hx hy heq


-- created on 2026-10-22
