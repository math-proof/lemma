import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_11_5
open Chapter11.BoundedInterval
open Chapter9
open Chapter11


/--
[integ_of_cts](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_5.lean)
-/
@[path]
private lemma main
  {a b:ℝ}
  {f:ℝ → ℝ}
-- given
  (hf: ContinuousOn f (Icc a b)) :
-- imply
  IntegrableOn f (Icc a b) :=
-- proof
  Chapter11.integ_of_cts hf


-- created on 2026-10-22
