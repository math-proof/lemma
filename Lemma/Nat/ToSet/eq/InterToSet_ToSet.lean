import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval
open Box


/--
[Box.inter](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B₁ B₂ : Box d} :
-- imply
  ∃ B : Box d, B.toSet = B₁.toSet ∩ B₂.toSet :=
-- proof
  Box.inter B₁ B₂


-- created on 2026-10-22
