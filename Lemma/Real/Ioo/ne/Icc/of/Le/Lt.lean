import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval


/--
[Ioo_ne_Icc](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {a₁ b₁ a₂ b₂ : ℝ}
-- given
  (ha₁b₁ : a₁ < b₁)
  (ha₂b₂ : a₂ ≤ b₂) :
-- imply
  Set.Ioo a₁ b₁ ≠ Set.Icc a₂ b₂ :=
-- proof
  BoundedInterval.Ioo_ne_Icc ha₁b₁ ha₂b₂


-- created on 2026-10-22
