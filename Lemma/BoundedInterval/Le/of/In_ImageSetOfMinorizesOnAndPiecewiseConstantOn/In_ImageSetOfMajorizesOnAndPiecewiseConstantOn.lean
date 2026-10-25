import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_11_3.Part5
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[integral_bound_lower_le_upper](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_3.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {a b:ℝ}
-- given
  (ha: a ∈ (PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})
  (hb: b ∈ (PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}) :
-- imply
  b ≤ a :=
-- proof
  Chapter11.integral_bound_lower_le_upper ha hb


-- created on 2026-10-22
