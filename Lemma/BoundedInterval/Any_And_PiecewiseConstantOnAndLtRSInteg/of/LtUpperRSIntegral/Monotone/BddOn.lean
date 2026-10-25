import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_11_8.Part7
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[lt_of_gt_upper_RS_integral](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {α: ℝ → ℝ}
  {X:ℝ}
-- given
  (hf: BddOn f I)
  (hα: Monotone α)
  (hX: upper_RS_integral f I α < X ) :
-- imply
  ∃ g, MajorizesOn g f I ∧ PiecewiseConstantOn g I ∧ PiecewiseConstantOn.RS_integ g I α < X :=
-- proof
  Chapter11.lt_of_gt_upper_RS_integral hf hα hX


-- created on 2026-10-22
