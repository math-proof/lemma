import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_2
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.PiecewiseConstantOn


/--
[PiecewiseConstantOn.congr'](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean)
-/
@[path]
private lemma main
  {f g: ℝ → ℝ}
  {I: BoundedInterval}
-- given
  (hf: PiecewiseConstantOn f I)
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) :
-- imply
  PiecewiseConstantOn g I :=
-- proof
  Chapter11.PiecewiseConstantOn.congr' hf h


-- created on 2026-10-22
