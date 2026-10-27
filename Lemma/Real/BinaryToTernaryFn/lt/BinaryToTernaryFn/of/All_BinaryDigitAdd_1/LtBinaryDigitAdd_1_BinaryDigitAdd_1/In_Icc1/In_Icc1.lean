import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open Remark_1_3_10


/--
[binaryToTernary_lt_of_digit_lt](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {x y : ℝ}
  {k : ℕ}
-- given
  (hx : x ∈ Set.Icc (0:ℝ) 1)
  (hy : y ∈ Set.Icc (0:ℝ) 1)
  (hk_lt : binaryDigit x (k + 1) < binaryDigit y (k + 1))
  (hk_eq : ∀ j < k, binaryDigit x (j + 1) = binaryDigit y (j + 1)) :
-- imply
  binaryToTernaryFn x < binaryToTernaryFn y :=
-- proof
  Remark_1_3_10.binaryToTernary_lt_of_digit_lt hx hy k hk_lt hk_eq


-- created on 2026-10-22
