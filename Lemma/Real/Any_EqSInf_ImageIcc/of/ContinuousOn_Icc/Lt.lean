import Mathlib
import sympy.Basic
import sympy.analysis.Section_9_6
open Chapter9
open Chapter9.sInf


/--
[sInf.of_continuous_on_compact](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_6.lean)
-/
@[path]
private lemma main
  {a b:ℝ}
  {f:ℝ → ℝ}
-- given
  (h:a < b)
  (hf: ContinuousOn f (.Icc a b)) :
-- imply
  ∃ xmin ∈ Set.Icc a b, sInf (f '' .Icc a b) = f xmin :=
-- proof
  Chapter9.sInf.of_continuous_on_compact h f hf


-- created on 2026-10-22
