import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_3
open BoundedInterval
open UpperDarbouxIntegral


/--
[UpperDarbouxIntegral.bddBelow_neg](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {M: ℝ}
-- given
  (hM: ∀ x ∈ I, |f x| ≤ M) :
-- imply
  BddBelow ({ R | ∃ h: PiecewiseConstantFunction I, h.integral = R ∧ ∀ x ∈ I.toSet, (-f) x ≤ h.f x } : Set ℝ) :=
-- proof
  UpperDarbouxIntegral.bddBelow_neg M hM


-- created on 2026-10-22
