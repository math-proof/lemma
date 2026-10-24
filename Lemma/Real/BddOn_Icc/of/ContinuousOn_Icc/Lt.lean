import Mathlib
import sympy.Basic
import sympy.analysis.Section_9_6
open Chapter9
open Chapter9.BddOn


/--
[BddOn.of_continuous_on_compact](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_6.lean)
-/
@[path]
private lemma main
  {a b:ℝ}
  {f:ℝ → ℝ}
-- given
  (h:a < b)
  (hf: ContinuousOn f (.Icc a b) ) :
-- imply
  BddOn f (.Icc a b) :=
-- proof
  Chapter9.BddOn.of_continuous_on_compact h hf


-- created on 2026-10-22
