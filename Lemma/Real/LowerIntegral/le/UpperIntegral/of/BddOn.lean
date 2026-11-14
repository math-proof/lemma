import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_11_3.Part5
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[lower_integral_le_upper](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_3.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
-- given
  (h: BddOn f I) :
-- imply
  lower_integral f I ≤ upper_integral f I :=
-- proof
  Chapter11.lower_integral_le_upper h


-- created on 2026-10-22
