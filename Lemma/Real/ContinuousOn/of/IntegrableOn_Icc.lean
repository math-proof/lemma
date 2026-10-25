import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_11_9.Part3
open Chapter9 Chapter10 Chapter11.BoundedInterval
open Chapter11


/--
[cts_of_integ](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_9.lean)
-/
@[path]
private lemma main
  {a b:ℝ}
  {f:ℝ → ℝ}
-- given
  (hf: IntegrableOn f (Icc a b)) :
-- imply
  ContinuousOn (fun x => integ f (Icc a x)) (.Icc a b) :=
-- proof
  Chapter11.cts_of_integ hf


-- created on 2026-10-22
