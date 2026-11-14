import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval
open LowerDarbouxIntegral


/--
[LowerDarbouxIntegral.bddAbove](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {M: ℝ}
-- given
  (hM: ∀ x ∈ I, |f x| ≤ M) :
-- imply
  BddAbove ({ R | ∃ g: PiecewiseConstantFunction I, g.integral = R ∧ ∀ x ∈ I.toSet, g.f x ≤ f x } : Set ℝ) :=
-- proof
  LowerDarbouxIntegral.bddAbove M hM


-- created on 2026-10-22
