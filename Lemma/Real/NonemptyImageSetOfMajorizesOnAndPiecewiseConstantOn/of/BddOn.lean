import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_11_3.Part5
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[integral_bound_upper_nonempty](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_3.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
-- given
  (h: BddOn f I) :
-- imply
  ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty :=
-- proof
  Chapter11.integral_bound_upper_nonempty h


-- created on 2026-10-22
