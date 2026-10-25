import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_11_3.Part5
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[lt_of_gt_upper_integral](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_3.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {X:ℝ}
-- given
  (hf: BddOn f I)
  (hX: upper_integral f I < X ) :
-- imply
  ∃ g, MajorizesOn g f I ∧ PiecewiseConstantOn g I ∧ PiecewiseConstantOn.integ g I < X :=
-- proof
  Chapter11.lt_of_gt_upper_integral hf hX


-- created on 2026-10-22
