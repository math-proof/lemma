import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_11_8.Part7
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[gt_of_lt_lower_RS_integral](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {α:ℝ → ℝ}
  {X:ℝ}
-- given
  (hf: BddOn f I)
  (hα: Monotone α)
  (hX: X < lower_RS_integral f I α) :
-- imply
  ∃ h, MinorizesOn h f I ∧ PiecewiseConstantOn h I ∧ X < PiecewiseConstantOn.RS_integ h I α :=
-- proof
  Chapter11.gt_of_lt_lower_RS_integral hf hα hX


-- created on 2026-10-22
