import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_11_3.Part5
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[integ_le_lower_integral](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_3.lean)
-/
@[path]
private lemma main
  {f h:ℝ → ℝ}
  {I: BoundedInterval}
-- given
  (hf: BddOn f I)
  (hfh: MinorizesOn h f I)
  (hg: PiecewiseConstantOn h I) :
-- imply
  hg.integ' ≤ lower_integral f I :=
-- proof
  Chapter11.integ_le_lower_integral hf hfh hg


-- created on 2026-10-22
