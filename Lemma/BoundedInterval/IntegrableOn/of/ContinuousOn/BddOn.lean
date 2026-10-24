import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_5
open Chapter11.BoundedInterval
open Chapter9
open Chapter11


/--
[integ_of_bdd_cts](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_5.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {f:ℝ → ℝ}
-- given
  (hbound: BddOn f I)
  (hf: ContinuousOn f I) :
-- imply
  IntegrableOn f I :=
-- proof
  Chapter11.integ_of_bdd_cts hbound hf


-- created on 2026-10-22
