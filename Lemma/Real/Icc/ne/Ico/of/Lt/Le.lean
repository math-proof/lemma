import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval


/--
[Icc_ne_Ico](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {a₁ b₁ a₂ b₂ : ℝ}
-- given
  (ha₁b₁ : a₁ ≤ b₁)
  (ha₂b₂ : a₂ < b₂) :
-- imply
  Set.Icc a₁ b₁ ≠ Set.Ico a₂ b₂ :=
-- proof
  BoundedInterval.Icc_ne_Ico ha₁b₁ ha₂b₂


-- created on 2026-10-22
