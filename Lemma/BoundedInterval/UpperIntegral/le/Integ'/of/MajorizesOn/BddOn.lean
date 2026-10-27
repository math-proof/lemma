import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_11_3.Part5
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[upper_integral_le_integ](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_3.lean)
-/
@[path]
private lemma main
  {f g:ℝ → ℝ}
  {I: BoundedInterval}
-- given
  (hf: BddOn f I)
  (hfg: MajorizesOn g f I)
  (hg: PiecewiseConstantOn g I) :
-- imply
  upper_integral f I ≤ hg.integ' :=
-- proof
  Chapter11.upper_integral_le_integ hf hfg hg


-- created on 2026-10-22
