import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_11_8.Part7
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[upper_RS_integral_le_integ](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {f g:ℝ → ℝ}
  {I: BoundedInterval}
  {α:ℝ → ℝ}
-- given
  (hf: BddOn f I)
  (hfg: MajorizesOn g f I)
  (hg: PiecewiseConstantOn g I)
  (hα: Monotone α) :
-- imply
  upper_RS_integral f I α ≤ PiecewiseConstantOn.RS_integ g I α :=
-- proof
  Chapter11.upper_RS_integral_le_integ hf hfg hg hα


-- created on 2026-10-22
