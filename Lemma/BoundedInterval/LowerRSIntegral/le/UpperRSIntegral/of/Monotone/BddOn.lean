import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_11_8.Part7
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[lower_RS_integral_le_upper](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {α:ℝ → ℝ}
-- given
  (h: BddOn f I)
  (hα: Monotone α) :
-- imply
  lower_RS_integral f I α ≤ upper_RS_integral f I α :=
-- proof
  Chapter11.lower_RS_integral_le_upper h hα


-- created on 2026-10-22
