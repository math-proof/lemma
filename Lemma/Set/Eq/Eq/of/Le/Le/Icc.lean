import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval


/--
[Icc_eq_endpoints](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {a₁ b₁ a₂ b₂ : ℝ}
-- given
  (h : Set.Icc a₁ b₁ = Set.Icc a₂ b₂)
  (ha₁b₁ : a₁ ≤ b₁)
  (ha₂b₂ : a₂ ≤ b₂) :
-- imply
  a₁ = a₂ ∧ b₁ = b₂ :=
-- proof
  BoundedInterval.Icc_eq_endpoints h ha₁b₁ ha₂b₂


-- created on 2026-10-22
