import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_11_9.Part3
open Chapter9 Chapter10 Chapter11.BoundedInterval
open Chapter11
open Chapter11.DifferentiableOn


/--
[DifferentiableOn.of_F_11_9_2](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_9.lean)
-/
@[path]
private lemma main
  {x:ℝ}
-- given
  (hx: ¬ ∃ r:ℚ, x = r)
  (hx': x ∈ Set.Icc 0 1) :
-- imply
  DifferentiableWithinAt ℝ F_11_9_2 (.Icc 0 1) x :=
-- proof
  Chapter11.DifferentiableOn.of_F_11_9_2 hx hx'


-- created on 2026-10-22
