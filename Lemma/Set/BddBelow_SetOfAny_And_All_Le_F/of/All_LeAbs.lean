import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval
open UpperDarbouxIntegral


/--
[UpperDarbouxIntegral.bddBelow](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {M: ℝ}
-- given
  (hM: ∀ x ∈ I, |f x| ≤ M) :
-- imply
  BddBelow ({ R | ∃ h: PiecewiseConstantFunction I, h.integral = R ∧ ∀ x ∈ I.toSet, f x ≤ h.f x } : Set ℝ) :=
-- proof
  UpperDarbouxIntegral.bddBelow M hM


-- created on 2026-10-22
