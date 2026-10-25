import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval
open UpperDarbouxIntegral


/--
[UpperDarbouxIntegral.neg](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
-- given
  (hbound: ∃ M, ∀ x ∈ I, |f x| ≤ M) :
-- imply
  UpperDarbouxIntegral (-f) I = -LowerDarbouxIntegral f I :=
-- proof
  UpperDarbouxIntegral.neg hbound


-- created on 2026-10-22
