import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_3
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[integ_on_subsingleton](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_3.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
-- given
  (hI: |I|ₗ = 0) :
-- imply
  IntegrableOn f I ∧ integ f I = 0 :=
-- proof
  Chapter11.integ_on_subsingleton hI


-- created on 2026-10-22
