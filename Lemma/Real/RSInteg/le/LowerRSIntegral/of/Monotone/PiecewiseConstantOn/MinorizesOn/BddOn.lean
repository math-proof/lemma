import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_11_8.Part7
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[integ_le_lower_RS_integral](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {f h:ℝ → ℝ}
  {I: BoundedInterval}
  {α:ℝ → ℝ}
-- given
  (hf: BddOn f I)
  (hfh: MinorizesOn h f I)
  (hg: PiecewiseConstantOn h I)
  (hα: Monotone α) :
-- imply
  PiecewiseConstantOn.RS_integ h I α ≤ lower_RS_integral f I α :=
-- proof
  Chapter11.integ_le_lower_RS_integral hf hfh hg hα


-- created on 2026-10-22
