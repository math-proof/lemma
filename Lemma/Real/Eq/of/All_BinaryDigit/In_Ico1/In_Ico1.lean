import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open Remark_1_3_10


/--
[eq_of_binaryDigit_eq_of_non_dyadic](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {x₁ x₂ : ℝ}
-- given
  (hx₁ : x₁ ∈ Set.Ico (0:ℝ) 1)
  (hx₂ : x₂ ∈ Set.Ico (0:ℝ) 1)
  (hnd₁ : x₁ ∉ DyadicRationals)
  (hnd₂ : x₂ ∉ DyadicRationals)
  (heq : ∀ j, binaryDigit x₁ j = binaryDigit x₂ j) :
-- imply
  x₁ = x₂ :=
-- proof
  Remark_1_3_10.eq_of_binaryDigit_eq_of_non_dyadic hx₁ hx₂ hnd₁ hnd₂ heq


-- created on 2026-10-22
