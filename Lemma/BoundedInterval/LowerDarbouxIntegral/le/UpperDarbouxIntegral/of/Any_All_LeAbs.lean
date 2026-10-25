import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval


/--
[lower_darboux_le_upper_darboux](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
-- given
  (hbound: ∃ M, ∀ x ∈ I, |f x| ≤ M) :
-- imply
  LowerDarbouxIntegral f I ≤ UpperDarbouxIntegral f I :=
-- proof
  lower_darboux_le_upper_darboux hbound


-- created on 2026-10-22
