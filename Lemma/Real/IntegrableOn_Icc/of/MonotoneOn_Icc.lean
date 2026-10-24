import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_6
open Chapter9 Chapter11.BoundedInterval
open Chapter11


/--
[integ_of_monotone](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_6.lean)
-/
@[path]
private lemma main
  {a b:ℝ}
  {f:ℝ → ℝ}
-- given
  (hf: MonotoneOn f (Icc a b)) :
-- imply
  IntegrableOn f (Icc a b) :=
-- proof
  Chapter11.integ_of_monotone hf


-- created on 2026-10-22
