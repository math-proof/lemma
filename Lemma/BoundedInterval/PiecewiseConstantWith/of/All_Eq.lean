import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_11_2.Part6
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.PiecewiseConstantWith


/--
[PiecewiseConstantWith.congr](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean)
-/
@[path]
private lemma main
  {f g:ℝ → ℝ}
  {I: BoundedInterval}
  {P: Partition I}
-- given
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) :
-- imply
  PiecewiseConstantWith f P ↔ PiecewiseConstantWith g P :=
-- proof
  Chapter11.PiecewiseConstantWith.congr h


-- created on 2026-10-22
