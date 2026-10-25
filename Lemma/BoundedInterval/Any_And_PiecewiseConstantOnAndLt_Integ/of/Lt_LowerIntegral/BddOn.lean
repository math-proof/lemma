import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_11_3.Part5
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[gt_of_lt_lower_integral](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_3.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {X:ℝ}
-- given
  (hf: BddOn f I)
  (hX: X < lower_integral f I) :
-- imply
  ∃ h, MinorizesOn h f I ∧ PiecewiseConstantOn h I ∧ X < PiecewiseConstantOn.integ h I :=
-- proof
  Chapter11.gt_of_lt_lower_integral hf hX


-- created on 2026-10-22
